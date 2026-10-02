// Web proxy v2: faster (streaming, compression, caching, DNS cache) and more compatible
// (cookie jar, range requests for video, single-page-app fixes).
// Run:  node server.js     (Node 18+, no dependencies)  ->  http://localhost:3000
const http = require('http');
const dns = require('dns').promises;
const net = require('net');
const zlib = require('zlib');
const crypto = require('crypto');
const { Readable, pipeline } = require('stream');

const PORT = process.env.PORT || 3000;
const enc = (u) => '/p?u=' + encodeURIComponent(u);
const TEXTY = /text|json|javascript|xml|svg/i;

// Optional password: set a PASSWORD environment variable on your host to require it.
const PASSWORD = process.env.PASSWORD || '';
function authed(req) {
  if (!PASSWORD) return true;
  const m = /^Basic (.+)$/i.exec(req.headers.authorization || '');
  if (!m) return false;
  const given = Buffer.from(Buffer.from(m[1], 'base64').toString().split(':').slice(1).join(':'));
  const want = Buffer.from(PASSWORD);
  return given.length === want.length && crypto.timingSafeEqual(given, want);
}

// ---------- safety: block private/internal addresses (lookups cached for 60s) ----------
const dnsCache = new Map();
async function isPrivate(host) {
  const hit = dnsCache.get(host);
  if (hit && hit.exp > Date.now()) return hit.bad;
  let bad = true;
  try {
    const { address } = await dns.lookup(host);
    if (net.isIPv4(address)) {
      const [a, b] = address.split('.').map(Number);
      bad = a === 0 || a === 10 || a === 127 || (a === 169 && b === 254) ||
        (a === 172 && b >= 16 && b <= 31) || (a === 192 && b === 168);
    } else bad = address === '::1' || /^(fc|fd|fe80)/i.test(address);
  } catch {}
  dnsCache.set(host, { bad, exp: Date.now() + 60000 });
  return bad;
}

// ---------- cookie jar: site cookies stay on the server, one jar per visitor ----------
const jars = new Map();
function visitor(req, res) {
  const m = /(?:^|;\s*)px=([\w-]+)/.exec(req.headers.cookie || '');
  if (m) return m[1];
  const id = crypto.randomUUID();
  res.setHeader('set-cookie', `px=${id}; Path=/; HttpOnly; SameSite=Lax; Max-Age=31536000`);
  if (jars.size > 500) jars.delete(jars.keys().next().value);
  return id;
}
const domainOk = (host, d) => host === d || host.endsWith('.' + d);
function cookieHeader(jar, t) {
  const now = Date.now();
  return jar.filter((c) => (!c.exp || c.exp > now) && domainOk(t.hostname, c.domain) && t.pathname.startsWith(c.path))
    .map((c) => c.name + '=' + c.value).join('; ');
}
function storeCookies(jar, t, lines) {
  for (const line of lines) {
    const [pair, ...attrs] = line.split(';');
    const i = pair.indexOf('=');
    if (i < 1) continue;
    const c = { name: pair.slice(0, i).trim(), value: pair.slice(i + 1).trim(), domain: t.hostname, path: '/', exp: 0 };
    for (const a of attrs) {
      const [k, v = ''] = a.trim().split('=');
      const key = k.toLowerCase();
      if (key === 'domain') c.domain = v.replace(/^\./, '').toLowerCase();
      else if (key === 'path') c.path = v || '/';
      else if (key === 'max-age') c.exp = Date.now() + Number(v) * 1000;
      else if (key === 'expires' && !c.exp) c.exp = Date.parse(v) || 0;
    }
    if (!domainOk(t.hostname, c.domain)) continue;
    const k = jar.findIndex((x) => x.name === c.name && x.domain === c.domain && x.path === c.path);
    if (k >= 0) jar.splice(k, 1);
    if (!c.exp || c.exp > Date.now()) jar.push(c);
  }
}

// ---------- cache for small static files (images, fonts, css, js): 10 min, 100 MB max ----------
const cache = new Map();
let cacheBytes = 0;
function cacheGet(k) {
  const e = cache.get(k);
  if (!e) return null;
  if (e.exp > Date.now()) return e;
  cache.delete(k); cacheBytes -= e.body.length;
  return null;
}
function cachePut(k, e) {
  if (cache.has(k)) cacheBytes -= cache.get(k).body.length;
  cache.set(k, e); cacheBytes += e.body.length;
  while (cacheBytes > 1e8) { const [k0, v0] = cache.entries().next().value; cache.delete(k0); cacheBytes -= v0.body.length; }
}

// ---------- rewriting ----------
function rw(raw, base) {
  raw = raw.trim().replace(/&amp;/g, '&');
  if (!raw || /^(data:|blob:|javascript:|mailto:|tel:|about:|#)/i.test(raw)) return raw;
  try { return enc(new URL(raw, base).href); } catch { return raw; }
}

const rewriteCss = (css, base) => css
  .replace(/url\(\s*(['"]?)(.*?)\1\s*\)/gi, (m, q, u) => `url(${q}${rw(u, base)}${q})`)
  .replace(/@import\s+(['"])(.*?)\1/gi, (m, q, u) => `@import ${q}${rw(u, base)}${q}`);

// Runs inside every proxied page so its scripts keep working through the proxy.
function clientScript(base) {
  const fn = function (B) {
    var P = '/p?u=', skip = /^(data:|blob:|javascript:|mailto:|tel:|about:|#)/i;
    function px(u) {
      if (u == null) return u;
      u = String(u);
      if (skip.test(u) || u.indexOf(P) === 0) return u;
      try { return P + encodeURIComponent(new URL(u, B).href); } catch (e) { return u; }
    }
    function note() { if (top !== window && parent === top) parent.postMessage({ proxied: B }, '*'); }

    // Service workers would hijack the proxy, and "offline" screens come from navigator.onLine.
    try {
      Object.defineProperty(Navigator.prototype, 'onLine', { get: function () { return true; }, configurable: true });
      if (navigator.serviceWorker) navigator.serviceWorker.register = function () {
        return Promise.reject(new DOMException('Service workers are disabled', 'SecurityError'));
      };
    } catch (e) {}

    var _fetch = window.fetch;
    window.fetch = function (i, o) {
      if (typeof i === 'string' || i instanceof URL) i = px(i);
      else if (i && i.url) i = new Request(px(i.url), i);
      return _fetch.call(this, i, o);
    };
    var _xo = XMLHttpRequest.prototype.open;
    XMLHttpRequest.prototype.open = function (m, u) { arguments[1] = px(u); return _xo.apply(this, arguments); };
    var _bc = navigator.sendBeacon;
    if (_bc) navigator.sendBeacon = function (u, d) { return _bc.call(navigator, px(u), d); };
    var _wo = window.open;
    window.open = function (u) { if (u) arguments[0] = px(u); return _wo.apply(this, arguments); };
    var _W = window.Worker;
    if (_W) { window.Worker = function (u, o) { return new _W(px(u), o); }; window.Worker.prototype = _W.prototype; }

    // Single-page apps change the address with pushState; keep it on the proxy and track the real URL.
    ['pushState', 'replaceState'].forEach(function (k) {
      var o = History.prototype[k];
      History.prototype[k] = function (s, t, u) {
        if (u != null && String(u).indexOf(P) !== 0) { try { B = new URL(u, B).href; } catch (e) {} }
        var r = o.call(this, s, t, px(u));
        note();
        return r;
      };
    });

    // Elements whose src/href are set from script (img.src = ...) also go through the proxy.
    [[HTMLImageElement, 'src'], [HTMLScriptElement, 'src'], [HTMLIFrameElement, 'src'], [HTMLMediaElement, 'src'],
     [HTMLSourceElement, 'src'], [HTMLLinkElement, 'href'], [HTMLAnchorElement, 'href']].forEach(function (e) {
      var d = Object.getOwnPropertyDescriptor(e[0].prototype, e[1]);
      if (d && d.set) Object.defineProperty(e[0].prototype, e[1], {
        get: d.get, set: function (v) { d.set.call(this, px(v)); }, configurable: true, enumerable: d.enumerable
      });
    });
    var _set = Element.prototype.setAttribute;
    Element.prototype.setAttribute = function (n, v) {
      if (/^(src|href|poster)$/i.test(n)) v = px(v);
      return _set.call(this, n, v);
    };

    // Links and forms that target the top window would leave the proxy page; keep them inside it.
    document.addEventListener('click', function (e) {
      var a = e.target.closest && e.target.closest('a[target]');
      if (a && /^_(top|parent)$/i.test(a.target)) a.target = '_self';
    }, true);
    document.addEventListener('submit', function (e) {
      var f = e.target, a = new URL(f.getAttribute('action') || B, B);
      if (/^_(top|parent)$/i.test(f.target)) f.target = '_self';
      if ((f.method || 'get').toLowerCase() === 'get') {
        e.preventDefault();
        a.search = new URLSearchParams(new FormData(f)).toString();
        location.href = px(a.href);
      } else f.action = px(a.href);
    }, true);
    note();
  };
  return `<script>(${fn})(${JSON.stringify(base).replace(/</g, '\\u003c')})</script>`;
}

function rewriteHtml(html, base) {
  html = html
    .replace(/<base\b[^>]*>/gi, '')
    .replace(/<meta[^>]+http-equiv=["']?content-security-policy[^>]*>/gi, '')
    .replace(/(<meta[^>]+http-equiv=["']?refresh[^>]+content=["']\s*\d+\s*;\s*url=)([^"']+)/gi, (m, a, u) => a + rw(u, base))
    .replace(/\s(integrity|nonce)=("[^"]*"|'[^']*')/gi, '')
    .replace(/\s(href|src|poster|data-src)=("([^"]*)"|'([^']*)')/gi,
      (m, attr, val, d, s) => ` ${attr}=${val[0]}${rw(d ?? s, base)}${val[0]}`)
    .replace(/\ssrcset=("([^"]*)"|'([^']*)')/gi, (m, val, d, s) =>
      ` srcset=${val[0]}${(d ?? s).split(',').map((p) => {
        const [u, ...rest] = p.trim().split(/\s+/);
        return [rw(u, base), ...rest].join(' ');
      }).join(', ')}${val[0]}`)
    .replace(/<style\b[^>]*>([\s\S]*?)<\/style>/gi, (m, css) => m.replace(css, () => rewriteCss(css, base)));
  const inject = clientScript(base);
  return /<head[^>]*>/i.test(html) ? html.replace(/<head[^>]*>/i, (m) => m + inject) : inject + html;
}

// ---------- server ----------
// Sends a buffer, compressing text with brotli/gzip when the browser supports it.
function sendBuf(req, res, code, type, buf, extra = {}) {
  const h = { 'content-type': type, 'access-control-allow-origin': '*', vary: 'accept-encoding', ...extra };
  const ae = req.headers['accept-encoding'] || '';
  if (buf.length > 1024 && TEXTY.test(type)) {
    if (/\bbr\b/.test(ae)) {
      h['content-encoding'] = 'br';
      buf = zlib.brotliCompressSync(buf, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 4 } });
    } else if (/\bgzip\b/.test(ae)) {
      h['content-encoding'] = 'gzip';
      buf = zlib.gzipSync(buf, { level: 6 });
    }
  }
  h['content-length'] = buf.length;
  res.writeHead(code, h);
  res.end(buf);
}
const text = (req, res, code, msg) => sendBuf(req, res, code, 'text/plain; charset=utf-8', Buffer.from(msg));

// Request headers we never forward upstream (the proxy sets its own).
const DROP = /^(host|cookie|origin|referer|connection|content-length|accept-encoding|upgrade|transfer-encoding|te|keep-alive|expect|sec-|x-forwarded|forwarded|via|x-real-ip|cf-|fly-|render-|x-render|x-request-id|x-koyeb|x-envoy|x-amzn|traceparent|tracestate|cdn-loop|true-client-ip)/i;

http.createServer(async (req, res) => {
  if (!authed(req)) {
    res.writeHead(401, { 'www-authenticate': 'Basic realm="Passage"', 'content-type': 'text/plain' });
    return res.end('Password required');
  }
  const url = new URL(req.url, 'http://localhost');
  if (url.pathname === '/') return sendBuf(req, res, 200, 'text/html; charset=utf-8', Buffer.from(UI));

  const target = url.pathname === '/p' ? url.searchParams.get('u') : null;
  if (!target) {
    // A script built a root-relative URL (img.src = '/a.png'): resolve it against the page that asked.
    try {
      const base = new URL(req.headers.referer).searchParams.get('u');
      res.writeHead(302, { location: enc(new URL(req.url, base).href) });
      return res.end();
    } catch { return text(req, res, 404, 'Not found'); }
  }

  const vid = visitor(req, res);
  if (!jars.has(vid)) jars.set(vid, []);
  const jar = jars.get(vid);
  const ac = new AbortController();
  res.on('close', () => ac.abort());

  try {
    const t = new URL(target);
    if (!/^https?:$/.test(t.protocol) || await isPrivate(t.hostname)) return text(req, res, 403, 'Blocked address');

    const hit = req.method === 'GET' && !req.headers.range ? cacheGet(t.href) : null;
    if (hit) return sendBuf(req, res, 200, hit.type, hit.body, hit.extra);

    let body;
    if (!['GET', 'HEAD'].includes(req.method)) {
      const chunks = [];
      for await (const c of req) chunks.push(c);
      body = Buffer.concat(chunks);
    }

    const up = {};
    for (const [k, v] of Object.entries(req.headers)) {
      if (DROP.test(k) || (k === 'authorization' && PASSWORD && /^Basic /i.test(v))) continue;
      up[k] = v;
    }
    up['accept-encoding'] = req.headers.range ? 'identity' : 'gzip, deflate, br';
    up.referer = t.origin + '/';
    if (req.headers.origin || body) up.origin = t.origin;
    const ck = cookieHeader(jar, t);
    if (ck) up.cookie = ck;

    const r = await fetch(t, { method: req.method, body, redirect: 'manual', headers: up, signal: ac.signal });
    storeCookies(jar, t, r.headers.getSetCookie ? r.headers.getSetCookie() : []);

    // Redirects go back through the proxy so every hop is checked and rewritten.
    if (r.status >= 300 && r.status < 400 && r.headers.get('location')) {
      res.writeHead(r.status, { location: enc(new URL(r.headers.get('location'), t).href) });
      return res.end();
    }

    const type = r.headers.get('content-type') || 'application/octet-stream';
    const isHtml = /text\/html/i.test(type), isCss = /text\/css/i.test(type);
    const len = Number(r.headers.get('content-length')) || 0;
    const cacheable = req.method === 'GET' && !req.headers.range && r.status === 200 &&
      /image|font|css|javascript/i.test(type) && !/no-store|private/i.test(r.headers.get('cache-control') || '');

    // Pages and stylesheets need rewriting, so they are buffered. Small static files are buffered to be cached.
    if (isHtml || isCss || (cacheable && len && len < 2e6)) {
      let out = Buffer.from(await r.arrayBuffer()), outType = type;
      if (isHtml) { out = Buffer.from(rewriteHtml(out.toString('utf8'), t.href)); outType = 'text/html; charset=utf-8'; }
      else if (isCss) { out = Buffer.from(rewriteCss(out.toString('utf8'), t.href)); outType = 'text/css; charset=utf-8'; }
      const extra = {};
      if (!isHtml) for (const k of ['cache-control', 'etag', 'last-modified']) if (r.headers.get(k)) extra[k] = r.headers.get(k);
      if (cacheable) cachePut(t.href, { body: out, type: outType, extra, exp: Date.now() + 6e5 });
      return sendBuf(req, res, r.status, outType, out, extra);
    }

    // Everything else (video, audio, big files, scripts) streams straight through, with seeking support.
    const h = { 'content-type': type, 'access-control-allow-origin': '*' };
    for (const k of ['content-range', 'accept-ranges', 'etag', 'last-modified', 'cache-control', 'content-disposition']) {
      if (r.headers.get(k)) h[k] = r.headers.get(k);
    }
    if (len && !r.headers.get('content-encoding')) h['content-length'] = len;
    const gz = TEXTY.test(type) && r.status === 200 && /\bgzip\b/.test(req.headers['accept-encoding'] || '');
    if (gz) { h['content-encoding'] = 'gzip'; h.vary = 'accept-encoding'; delete h['content-length']; }
    res.writeHead(r.status, h);
    if (!r.body) return res.end();
    pipeline(Readable.fromWeb(r.body), ...(gz ? [zlib.createGzip()] : []), res, () => {});
  } catch (err) {
    if (!res.headersSent) text(req, res, 502, 'Could not load that site: ' + err.message);
    else res.end();
  }
}).listen(PORT, () => console.log(`Proxy running at http://localhost:${PORT}`));

// ---------- the page you see ----------
const UI = String.raw`<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Passage</title>
<style>
:root{--chrome:#dde4ec;--surface:#f8fafc;--ink:#14202e;--mute:#5b6b7c;--line:#c4cfdb;--acc:#3b49d6;--accInk:#fff;--tab:#cbd5e1}
@media (prefers-color-scheme:dark){:root{--chrome:#0e1319;--surface:#1a212b;--ink:#e8eef5;--mute:#93a1b2;--line:#2c3644;--acc:#8c9bff;--accInk:#0e1319;--tab:#161c24}}
*{box-sizing:border-box}
html,body{height:100%;margin:0}
body{display:flex;flex-direction:column;background:var(--chrome);color:var(--ink);font:15px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif;padding:env(safe-area-inset-top) env(safe-area-inset-right) env(safe-area-inset-bottom) env(safe-area-inset-left)}
[hidden]{display:none!important}
button,input{font:inherit;color:inherit}
#tabrow{display:flex;align-items:flex-end;gap:4px;padding:8px 8px 0}
#tabs{display:flex;gap:4px;overflow-x:auto;scrollbar-width:none;min-width:0}
.tab{display:flex;align-items:center;gap:8px;width:170px;height:36px;padding:0 6px 0 12px;border-radius:10px 10px 0 0;background:var(--tab);color:var(--mute);cursor:pointer;flex:0 0 auto}
.tab.on{background:var(--surface);color:var(--ink)}
.tab .t{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:13px}
.fav{width:16px;height:16px;border-radius:4px;flex:none;object-fit:cover}
.x{border:0;background:none;width:26px;height:26px;border-radius:7px;font-size:18px;line-height:1;cursor:pointer;flex:none}
.x:hover,.ib:hover{background:var(--chrome)}
#newtab{margin-bottom:5px;color:var(--ink)}
#tool{position:relative;display:flex;align-items:center;gap:4px;padding:8px;background:var(--surface);border-bottom:1px solid var(--line)}
.ib{border:0;background:none;width:36px;height:36px;border-radius:9px;font-size:19px;cursor:pointer;flex:none}
.ib:disabled{opacity:.35;cursor:default}
#q{flex:1;min-width:0;height:36px;border:1px solid var(--line);border-radius:18px;padding:0 16px;background:var(--chrome)}
#q:focus,#bigq:focus{outline:2px solid var(--acc);outline-offset:0;background:var(--surface)}
button:focus-visible{outline:2px solid var(--acc);outline-offset:1px}
#load{position:absolute;left:0;bottom:-1px;height:2px;width:0;opacity:0;background:var(--acc);transition:width .45s ease,opacity .3s}
#menu{position:absolute;right:8px;top:50px;z-index:5;min-width:220px;padding:6px;border:1px solid var(--line);border-radius:12px;background:var(--surface);box-shadow:0 10px 30px rgba(0,0,0,.18)}
#menu button{display:block;width:100%;text-align:left;border:0;background:none;padding:10px 12px;border-radius:8px;cursor:pointer}
#menu button:hover{background:var(--chrome)}
#stage{flex:1;position:relative;background:var(--surface);min-height:0}
iframe{position:absolute;inset:0;width:100%;height:100%;border:0;background:#fff}
#start{position:absolute;inset:0;overflow:auto;padding:9vh 20px 40px}
.wrap{max-width:660px;margin:0 auto}
h1{font:600 clamp(36px,8vw,60px)/1.02 Georgia,"Iowan Old Style",serif;letter-spacing:-.02em;margin:0 0 10px}
.sub{color:var(--mute);margin:0 0 22px}
#big{display:flex;gap:8px}
#bigq{flex:1;min-width:0;height:52px;border:1px solid var(--line);border-radius:26px;padding:0 22px;font-size:17px;background:var(--chrome)}
#big button{height:52px;padding:0 24px;border:0;border-radius:26px;background:var(--acc);color:var(--accInk);font-weight:600;cursor:pointer}
.tiles{display:grid;grid-template-columns:repeat(auto-fill,minmax(112px,1fr));gap:12px;margin-top:30px}
.tile{position:relative;display:flex;flex-direction:column;align-items:center;gap:8px;padding:18px 8px 14px;border:1px solid var(--line);border-radius:16px;background:var(--surface);cursor:pointer}
.tile:hover{border-color:var(--acc)}
.dot{display:grid;place-items:center;width:42px;height:42px;border-radius:50%;background:var(--chrome);font:600 18px Georgia,serif}
.name{max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:13px}
.rm{position:absolute;top:4px;right:6px;color:var(--mute);font-size:16px;line-height:1;padding:2px 5px;border-radius:6px}
.rm:hover{background:var(--chrome)}
h2{font-size:12px;letter-spacing:.08em;text-transform:uppercase;color:var(--mute);margin:30px 0 10px}
.chips{display:flex;flex-wrap:wrap;gap:8px}
.chip{border:1px solid var(--line);background:var(--surface);border-radius:999px;padding:5px 14px;font-size:13px;cursor:pointer}
.chip:hover{border-color:var(--acc);color:var(--acc)}
@media (max-width:560px){.tab{width:130px}#start{padding-top:5vh}}
</style></head>
<body>
<header>
  <div id="tabrow"><div id="tabs" role="tablist"></div><button class="x" id="newtab" aria-label="New tab">+</button></div>
  <form id="tool">
    <button type="button" class="ib" id="back" aria-label="Back">&#8592;</button>
    <button type="button" class="ib" id="fwd" aria-label="Forward">&#8594;</button>
    <button type="button" class="ib" id="rel" aria-label="Reload">&#8635;</button>
    <input id="q" placeholder="Search or enter a web address" autocomplete="off" autocapitalize="off" spellcheck="false" enterkeyhint="go">
    <button type="button" class="ib" id="star" aria-label="Bookmark this page">&#9734;</button>
    <button type="button" class="ib" id="more" aria-label="Menu">&#8943;</button>
    <div id="menu" hidden>
      <button type="button" id="closeall">Close all tabs</button>
      <button type="button" id="clear">Clear bookmarks and recent sites</button>
    </div>
    <div id="load"></div>
  </form>
</header>
<main id="stage">
  <section id="start">
    <div class="wrap">
      <h1>Where to?</h1>
      <p class="sub">Pages open inside this window. Tabs, bookmarks and recent sites are saved on this device.</p>
      <form id="big"><input id="bigq" placeholder="Search or enter a web address" autocomplete="off" autocapitalize="off" spellcheck="false" enterkeyhint="go"><button>Go</button></form>
      <div class="tiles" id="tiles"></div>
      <div id="recentbox"><h2>Recent</h2><div class="chips" id="recent"></div></div>
    </div>
  </section>
</main>
<script>
const $ = (s) => document.querySelector(s);
const store = {
  get(k, d) { try { const v = JSON.parse(localStorage.getItem(k)); return v == null ? d : v; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }
};
const DEFAULTS = [
  ['Wikipedia', 'https://wikipedia.org'], ['DuckDuckGo', 'https://html.duckduckgo.com/html/'],
  ['Hacker News', 'https://news.ycombinator.com'], ['Internet Archive', 'https://archive.org'],
  ['BBC', 'https://www.bbc.com'], ['GitHub', 'https://github.com']
];
let tabs = [], active = null, seq = 0;
let marks = store.get('marks', []), recent = store.get('recent', []);
const q = $('#q'), stage = $('#stage'), start = $('#start'), bar = $('#load');

const px = (u) => '/p?u=' + encodeURIComponent(u);
function host(u) { try { return new URL(u).hostname.replace(/^www[.]/, ''); } catch (e) { return u; } }
function el(tag, cls, text) {
  const n = document.createElement(tag);
  if (cls) n.className = cls;
  if (text != null) n.textContent = text;
  return n;
}
function norm(v) {
  v = v.trim();
  if (!v) return '';
  if (/^https?:[/][/]/i.test(v)) return v;
  if (/^[^\s]+[.][a-z]{2,}([/:?#]|$)/i.test(v)) return 'https://' + v;
  return 'https://html.duckduckgo.com/html/?q=' + encodeURIComponent(v);
}

// thin progress line under the toolbar
function busy(on) {
  clearTimeout(busy.t);
  if (on) {
    bar.style.opacity = 1; bar.style.width = '70%';
    busy.t = setTimeout(() => { bar.style.width = '90%'; }, 1500);
  } else {
    bar.style.width = '100%';
    busy.t = setTimeout(() => { bar.style.opacity = 0; bar.style.width = '0'; }, 300);
  }
}

function save() { store.set('tabs', tabs.map((t) => ({ url: t.url, title: t.title }))); }
function remember(u) {
  recent = [u].concat(recent.filter((x) => x !== u)).slice(0, 8);
  store.set('recent', recent);
}

function newTab(url) {
  const t = { id: ++seq, url: '', title: 'New tab', frame: null };
  tabs.push(t);
  select(t);
  if (url) go(url);
}
function ensureFrame(t) {
  if (!t.url || t.frame) return;
  const f = document.createElement('iframe');
  f.title = 'Page';
  f.allow = 'fullscreen; autoplay; encrypted-media; picture-in-picture; clipboard-write';
  f.allowFullscreen = true;
  f.onload = () => loaded(t);
  f.src = px(t.url);
  stage.appendChild(f);
  t.frame = f;
}
function select(t) {
  active = t;
  ensureFrame(t);
  tabs.forEach((x) => { if (x.frame) x.frame.hidden = x !== t; });
  start.hidden = !!t.url;
  q.value = t.url;
  render(); star(); renderStart(); save();
}
function go(v) {
  const u = norm(v);
  if (!u || !active) return;
  const t = active;
  t.url = u; t.title = host(u);
  remember(u);
  busy(true);
  if (t.frame) t.frame.src = px(u); else ensureFrame(t);
  select(t);
  q.blur();
}
function loaded(t) {
  if (t === active) busy(false);
  try {
    const w = t.frame.contentWindow;
    if (w.document.title) t.title = w.document.title;
    w.addEventListener('beforeunload', () => { if (t === active) busy(true); });
  } catch (e) {}
  render(); save();
}
function closeTab(t) {
  const i = tabs.indexOf(t);
  if (t.frame) t.frame.remove();
  tabs.splice(i, 1);
  if (!tabs.length) return newTab();
  if (t === active) select(tabs[Math.min(i, tabs.length - 1)]); else { render(); save(); }
}

function render() {
  const row = $('#tabs');
  row.textContent = '';
  tabs.forEach((t) => {
    const n = el('div', 'tab' + (t === active ? ' on' : ''));
    n.setAttribute('role', 'tab');
    if (t.url) {
      const i = el('img', 'fav');
      i.alt = '';
      try { i.src = px(new URL(t.url).origin + '/favicon.ico'); } catch (e) {}
      i.onerror = () => { i.style.visibility = 'hidden'; };
      n.appendChild(i);
    }
    n.appendChild(el('span', 't', t.title));
    const x = el('button', 'x', '\u00d7');
    x.type = 'button';
    x.setAttribute('aria-label', 'Close tab');
    x.onclick = (e) => { e.stopPropagation(); closeTab(t); };
    n.appendChild(x);
    n.onclick = () => select(t);
    row.appendChild(n);
  });
}

function star() {
  const ok = !!(active && active.url);
  const on = ok && marks.some((m) => m.url === active.url);
  $('#star').textContent = on ? '\u2605' : '\u2606';
  $('#star').disabled = !ok;
  ['back', 'fwd', 'rel'].forEach((id) => { $('#' + id).disabled = !(active && active.frame); });
}

function renderStart() {
  const grid = $('#tiles');
  grid.textContent = '';
  const items = marks.map((m) => ({ title: m.title, url: m.url, mark: true }))
    .concat(DEFAULTS.map((d) => ({ title: d[0], url: d[1] })));
  items.forEach((it) => {
    const b = el('button', 'tile');
    b.type = 'button';
    b.appendChild(el('span', 'dot', (host(it.url)[0] || '?').toUpperCase()));
    b.appendChild(el('span', 'name', it.title));
    b.onclick = () => go(it.url);
    if (it.mark) {
      const x = el('span', 'rm', '\u00d7');
      x.title = 'Remove bookmark';
      x.onclick = (e) => {
        e.stopPropagation();
        marks = marks.filter((m) => m.url !== it.url);
        store.set('marks', marks); star(); renderStart();
      };
      b.appendChild(x);
    }
    grid.appendChild(b);
  });
  const r = $('#recent');
  r.textContent = '';
  $('#recentbox').hidden = !recent.length;
  recent.forEach((u) => {
    const c = el('button', 'chip', host(u));
    c.type = 'button';
    c.onclick = () => go(u);
    r.appendChild(c);
  });
}

// pages report their real address (including in-page navigation) through postMessage
addEventListener('message', (e) => {
  const t = tabs.find((x) => x.frame && x.frame.contentWindow === e.source);
  if (!t || !e.data || !e.data.proxied) return;
  t.url = e.data.proxied;
  remember(t.url);
  if (t === active) { q.value = t.url; star(); }
  save();
});

$('#tool').onsubmit = (e) => { e.preventDefault(); go(q.value); };
$('#big').onsubmit = (e) => { e.preventDefault(); const b = $('#bigq'); go(b.value); b.value = ''; };
$('#newtab').onclick = () => newTab();
$('#back').onclick = () => { try { active.frame.contentWindow.history.back(); } catch (e) {} };
$('#fwd').onclick = () => { try { active.frame.contentWindow.history.forward(); } catch (e) {} };
$('#rel').onclick = () => { try { busy(true); active.frame.contentWindow.location.reload(); } catch (e) {} };
$('#star').onclick = () => {
  if (!active || !active.url) return;
  const i = marks.findIndex((m) => m.url === active.url);
  if (i >= 0) marks.splice(i, 1); else marks.unshift({ url: active.url, title: active.title });
  store.set('marks', marks); star(); renderStart();
};
$('#more').onclick = () => { $('#menu').hidden = !$('#menu').hidden; };
document.addEventListener('click', (e) => { if (!e.target.closest('#menu, #more')) $('#menu').hidden = true; });
$('#clear').onclick = () => {
  marks = []; recent = [];
  store.set('marks', []); store.set('recent', []);
  star(); renderStart(); $('#menu').hidden = true;
};
$('#closeall').onclick = () => {
  tabs.forEach((t) => { if (t.frame) t.frame.remove(); });
  tabs = []; $('#menu').hidden = true; newTab();
};

const saved = store.get('tabs', []);
if (saved.length) {
  saved.forEach((s) => tabs.push({ id: ++seq, url: s.url || '', title: s.title || 'New tab', frame: null }));
  select(tabs[0]);
} else newTab();
</script>
</body></html>`;
