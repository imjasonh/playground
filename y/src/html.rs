//! HTML/RSS rendering, post body formatting, and tiny helpers (dates, images).

use url::Url;

pub const POST_MAX_CHARS: usize = 260;

pub const PAPERCLIP_KEY: &str = "assets/paperclip.png";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Post {
    pub id: i64,
    pub body: String,
    pub created_at: i64,
    pub parent_id: Option<i64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PostImage {
    pub id: i64,
    pub post_id: i64,
    pub r2_key: String,
    pub content_type: String,
    pub width: Option<i64>,
    pub height: Option<i64>,
    pub alt: Option<String>,
    pub ordinal: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct YouTubeRef {
    pub id: String,
    pub start: Option<u32>,
}

pub fn escape_html(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

pub fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        return s.to_string();
    }
    let take = n.saturating_sub(1);
    let mut out: String = s.chars().take(take).collect();
    out.push('…');
    out
}

/// UTF-16 code units — matches HTML `maxlength` / the original JS `.length`.
pub fn utf16_len(s: &str) -> usize {
    s.encode_utf16().count()
}

pub fn img_url(site_url: &str, key: &str) -> String {
    let base = site_url.trim_end_matches('/');
    format!("{base}/img/{key}")
}

pub fn image_ext_for(content_type: &str) -> Option<&'static str> {
    match content_type {
        "image/jpeg" => Some("jpg"),
        "image/png" => Some("png"),
        "image/gif" => Some("gif"),
        "image/webp" => Some("webp"),
        "image/avif" => Some("avif"),
        _ => None,
    }
}

pub fn is_allowed_image_type(t: &str) -> bool {
    image_ext_for(t).is_some()
}

pub fn is_valid_email(s: &str) -> bool {
    if s.len() > 254 {
        return false;
    }
    let Some((user, rest)) = s.split_once('@') else {
        return false;
    };
    if user.is_empty() || user.contains(char::is_whitespace) {
        return false;
    }
    let Some((host, tld)) = rest.split_once('.') else {
        return false;
    };
    if host.is_empty() || tld.is_empty() {
        return false;
    }
    if rest.contains(char::is_whitespace) || rest.contains('@') {
        return false;
    }
    true
}

pub fn extract_youtube_ref(text: &str) -> Option<YouTubeRef> {
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if let Some(rest) = text[i..].strip_prefix("https://") {
            if let Some(ref_) = parse_youtube_from(rest) {
                return Some(ref_);
            }
        } else if let Some(rest) = text[i..].strip_prefix("http://") {
            if let Some(ref_) = parse_youtube_from(rest) {
                return Some(ref_);
            }
        }
        i += 1;
    }
    None
}

fn take_url_token(s: &str) -> &str {
    s.split(|c: char| c.is_whitespace() || "<>\"'`".contains(c))
        .next()
        .unwrap_or("")
}

fn parse_youtube_from(after_scheme: &str) -> Option<YouTubeRef> {
    let token = take_url_token(after_scheme);
    let url = Url::parse(&format!("https://{token}")).ok()?;
    parse_youtube_url(&url)
}

fn parse_youtube_url(u: &Url) -> Option<YouTubeRef> {
    let host = u
        .host_str()?
        .trim_start_matches("www.")
        .trim_start_matches("m.");
    let mut id: Option<String> = None;
    if host == "youtu.be" {
        id = u
            .path()
            .trim_start_matches('/')
            .split('/')
            .next()
            .filter(|s| !s.is_empty())
            .map(str::to_string);
    } else if host == "youtube.com" || host == "youtube-nocookie.com" {
        if u.path() == "/watch" {
            id = u
                .query_pairs()
                .find(|(k, _)| k == "v")
                .map(|(_, v)| v.into_owned());
        } else if let Some(rest) = u
            .path()
            .strip_prefix("/shorts/")
            .or_else(|| u.path().strip_prefix("/embed/"))
            .or_else(|| u.path().strip_prefix("/v/"))
        {
            id = rest.split('/').next().map(str::to_string);
        }
    }
    let id = id.filter(|s| is_yt_id(s))?;
    let start_str = u
        .query_pairs()
        .find(|(k, _)| k == "t" || k == "start")
        .map(|(_, v)| v.into_owned());
    let start = start_str
        .and_then(|s| parse_timestamp(&s))
        .filter(|n| *n > 0);
    Some(YouTubeRef { id, start })
}

fn is_yt_id(s: &str) -> bool {
    let n = s.len();
    (6..=15).contains(&n)
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
}

fn parse_timestamp(s: &str) -> Option<u32> {
    if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) {
        return s.parse().ok();
    }
    // 1h2m3s / 2m3s / 3s
    let mut rest = s;
    let mut total: u32 = 0;
    if let Some(idx) = rest.find('h') {
        let n: u32 = rest[..idx].parse().ok()?;
        total += n.saturating_mul(3600);
        rest = &rest[idx + 1..];
    }
    if let Some(idx) = rest.find('m') {
        let n: u32 = rest[..idx].parse().ok()?;
        total += n.saturating_mul(60);
        rest = &rest[idx + 1..];
    }
    if let Some(idx) = rest.find('s') {
        let n: u32 = rest[..idx].parse().ok()?;
        total += n;
        rest = &rest[idx + 1..];
    }
    if !rest.is_empty() || total == 0 {
        return None;
    }
    Some(total)
}

pub fn youtube_embed_src(ref_: &YouTubeRef) -> String {
    let base = format!("https://www.youtube-nocookie.com/embed/{}", ref_.id);
    match ref_.start {
        Some(s) => format!("{base}?start={s}"),
        None => base,
    }
}

pub fn youtube_thumbnail_url(ref_: &YouTubeRef) -> String {
    format!("https://img.youtube.com/vi/{}/hqdefault.jpg", ref_.id)
}

const TRAILING_PUNCT: &[char] = &[
    '.', ',', ';', ':', '!', '?', ')', ']', '}', '>', '\'', '"', '`',
];

/// Render a post body: fenced blocks, inline code, then bare http(s) URLs.
pub fn linkify_body(body: &str) -> String {
    let mut out = String::new();
    let mut rest = body;
    while !rest.is_empty() {
        let fence = rest.find("```");
        let tick = rest.find('`');
        let https = rest.find("https://");
        let http = rest.find("http://").filter(|&i| https != Some(i));
        let url = match (https, http) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };

        let next = [fence, tick, url].into_iter().flatten().min();
        let Some(at) = next else {
            out.push_str(&escape_html(rest));
            break;
        };
        out.push_str(&escape_html(&rest[..at]));
        rest = &rest[at..];

        if rest.starts_with("```") {
            if let Some(end) = rest[3..].find("```") {
                let mut inner = &rest[3..3 + end];
                if let Some(stripped) = inner.strip_prefix('\n') {
                    inner = stripped;
                } else if let Some(stripped) = inner.strip_prefix("\r\n") {
                    inner = stripped;
                }
                inner = inner.trim_end_matches('\n').trim_end_matches('\r');
                out.push_str("<pre><code>");
                out.push_str(&escape_html(inner));
                out.push_str("</code></pre>");
                rest = &rest[3 + end + 3..];
                continue;
            }
        }
        if rest.starts_with('`') && !rest.starts_with("```") {
            if let Some(end) = rest[1..].find('`') {
                let inner = &rest[1..1 + end];
                if !inner.is_empty() && !inner.contains('`') {
                    out.push_str("<code>");
                    out.push_str(&escape_html(inner));
                    out.push_str("</code>");
                    rest = &rest[1 + end + 1..];
                    continue;
                }
            }
        }
        if rest.starts_with("http://") || rest.starts_with("https://") {
            let token = take_url_token(rest);
            let mut url = token;
            let mut trailing = "";
            let trimmed = url.trim_end_matches(TRAILING_PUNCT);
            if trimmed.len() < url.len() && !trimmed.is_empty() {
                trailing = &url[trimmed.len()..];
                url = trimmed;
            }
            let escaped = escape_html(url);
            out.push_str("<a href=\"");
            out.push_str(&escaped);
            out.push_str("\" rel=\"noopener noreferrer\">");
            out.push_str(&escaped);
            out.push_str("</a>");
            out.push_str(&escape_html(trailing));
            rest = &rest[token.len()..];
            continue;
        }
        // Unmatched starter — emit one char and continue.
        let ch = rest.chars().next().unwrap();
        out.push_str(&escape_html(&ch.to_string()));
        rest = &rest[ch.len_utf8()..];
    }
    out
}

fn format_iso8601(unix: i64) -> String {
    let (y, m, d, hh, mm, ss) = civil_from_unix(unix);
    format!("{y:04}-{m:02}-{d:02}T{hh:02}:{mm:02}:{ss:02}.000Z")
}

pub fn format_rfc1123(unix: i64) -> String {
    const DOW: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
    const MON: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let (y, m, d, hh, mm, ss) = civil_from_unix(unix);
    let dow = unix_dow(unix);
    format!(
        "{dow}, {d:02} {mon} {y:04} {hh:02}:{mm:02}:{ss:02} GMT",
        dow = DOW[dow],
        mon = MON[(m - 1) as usize]
    )
}

fn unix_dow(unix: i64) -> usize {
    // 1970-01-01 was Thursday (4).
    let days = unix.div_euclid(86400);
    ((days + 4).rem_euclid(7)) as usize
}

fn civil_from_unix(unix: i64) -> (i32, u32, u32, u32, u32, u32) {
    let secs = unix.rem_euclid(86400) as u32;
    let hh = secs / 3600;
    let mm = (secs % 3600) / 60;
    let ss = secs % 60;
    let z = unix.div_euclid(86400) + 719_468;
    let era = z.div_euclid(146_097);
    let doe = (z - era * 146_097) as u32;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i32 + era as i32 * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y, m, d, hh, mm, ss)
}

const STYLE: &str = r#"
  :root { color-scheme: light; }
  body {
    font: 17px/1.55 'Courier Prime', 'American Typewriter', 'Courier New', Courier, monospace;
    margin: 0;
    padding: 2.5rem 1rem;
    min-height: 100vh;
    background: #bfb39a;
    color: #1a1410;
  }
  .paper {
    max-width: 640px;
    margin: 0 auto;
    background: #fdfaf2;
    padding: 3rem 3rem 2rem;
    box-shadow:
      0 1px 1px rgba(0, 0, 0, .15),
      0 6px 18px rgba(0, 0, 0, .25),
      0 22px 60px rgba(0, 0, 0, .2);
    position: relative;
  }
  header {
    display: flex; justify-content: space-between; align-items: baseline;
    margin-bottom: 2rem; padding-bottom: .75rem;
    border-bottom: 1px solid #c8b896;
  }
  header h1 { margin: 0; font-size: 1.6rem; font-weight: 400; letter-spacing: .02em; }
  header h1 a { color: inherit; text-decoration: none; }
  header nav a { margin-left: 1rem; font-size: 0.95rem; }
  a { color: #355176; text-decoration: underline; text-decoration-thickness: 1px; text-underline-offset: 2px; }
  a:hover { color: #1a3358; }
  .post { border-bottom: 1px dashed #c8b896; padding: 1.1rem 0; }
  .post:last-of-type { border-bottom: 0; }
  .post .postbody { margin: 0 0 .5rem; white-space: pre-wrap; word-wrap: break-word; }
  code {
    background: rgba(0, 0, 0, .06);
    padding: .05em .35em; border-radius: 2px;
  }
  .post .postbody pre {
    margin: .6rem 0; padding: .6rem .8rem;
    background: rgba(0, 0, 0, .06); border-radius: 2px;
    font: inherit; white-space: pre-wrap; word-wrap: break-word;
  }
  .post .postbody pre code { background: none; padding: 0; border-radius: 0; }
  .post .meta {
    font-size: .85rem; color: #7a6c55;
    display: flex; gap: .5rem; align-items: center;
  }
  .post .meta a { color: inherit; }
  .post .meta .actions {
    margin-left: auto; display: inline-flex; gap: 0;
    align-items: baseline;
  }
  .post .meta .actions form { display: inline; }
  .post .meta .actions a, .post .meta .actions button {
    font: inherit; color: inherit; cursor: pointer;
    background: transparent; border: 0; padding: 0; margin: 0;
    text-decoration: underline; text-underline-offset: 2px;
  }
  .post .meta .actions .sep { color: #c8b896; margin: 0 .4rem; user-select: none; }
  .post .meta .actions .time {
    font-size: .75rem; color: #a8997d; text-decoration: none;
  }
  .post .meta .actions .time:hover { text-decoration: underline; }
  .post.current { background: rgba(0,0,0,.04); border-left: 3px solid #8a7e62; padding-left: 1rem; }
  .thread-top { font-size: .9rem; margin: 0 0 1rem; }
  .reply-ctx { font-size: .9rem; color: #7a6c55; margin: 0 0 .5rem; }
  .reply-ctx a { color: inherit; }
  .post .meta .replies { color: inherit; text-decoration: none; }
  .post .meta .replies:hover { text-decoration: underline; }
  .post .images { display: flex; flex-wrap: wrap; gap: 2.5rem; margin: 1.5rem 0 1rem 0.5rem; padding: .5rem 0; }
  .post .images img { max-width: 100%; max-height: 320px; height: auto; width: auto; border-radius: 6px; }
  .post .clipped {
    position: relative; display: inline-block;
    padding: 8px 8px 12px;
    background: #fffefb;
    box-shadow:
      0 1px 2px rgba(0, 0, 0, .15),
      0 6px 14px rgba(0, 0, 0, .25);
    transform: rotate(2deg);
    transform-origin: 30% 50%;
  }
  .post .clipped img { display: block; max-width: 100%; max-height: 320px; }
  .post .clipped::before {
      content: '';
      position: absolute;
      top: 50%;
      left: -65px;
      width: 100px;
      height: 155px;
      transform: translateY(-50%) rotate(-95.7deg);
      background: url(/img/assets/paperclip.png) no-repeat center / contain;
      filter: drop-shadow(0 1px 1px rgba(0, 0, 0, .35));
      z-index: 2;
      pointer-events: none;
  }
  .post .yt { position: relative; padding-bottom: 56.25%; height: 0; margin: .5rem 0; overflow: hidden; }
  .post .yt iframe { position: absolute; top: 0; left: 0; width: 100%; height: 100%; border: 0; }
  .empty { color: #a8997d; font-style: italic; }
  .adminbar { margin: 0 0 1.5rem; }
  .admin-bottom { margin-top: 3rem; padding-top: 1rem; border-top: 1px dashed #c8b896; font-size: .9rem; }
  form { margin: 1rem 0; }
  textarea, input[type=text], input[type=email], input[type=password] {
    font: inherit; padding: .5rem; border: 1px dashed #a89a7e; border-radius: 0;
    width: 100%; box-sizing: border-box; background: rgba(0, 0, 0, .02); color: inherit;
  }
  textarea:focus, input:focus { outline: 1px solid #8a7e62; outline-offset: 1px; }
  textarea { min-height: 6rem; resize: vertical; }
  button, input[type=submit] {
    font: inherit; padding: 0; border: 0; background: transparent;
    color: #355176; cursor: pointer;
    text-decoration: underline; text-decoration-thickness: 1px; text-underline-offset: 2px;
  }
  button:hover, input[type=submit]:hover { color: #1a3358; }
  button.btn {
    padding: .4rem 1rem; border: 1px dashed #8a7e62;
    color: inherit; text-decoration: none;
  }
  button.btn:hover { background: rgba(0, 0, 0, .05); color: inherit; }
  .row { display: flex; gap: .5rem; align-items: center; }
  .row input[type=text], .row input[type=email] { flex: 1; }
  .err { color: #993333; }
  .ok  { color: #4a6b3a; }
  .counter { font-size: .85rem; color: #a8997d; margin-left: .5rem; }
  .counter .warn { color: #993333; font-weight: 600; }
  .interest-banner {
    margin: 0 0 1rem; padding: .6rem .9rem;
    border: 1px dashed #b89a3e; background: rgba(255, 224, 102, .25);
    font-size: .9rem;
  }
  footer {
    margin-top: 3rem; padding-top: 1rem; border-top: 1px dashed #c8b896;
    font-size: .85rem; color: #a8997d; text-align: center;
  }
"#;

/// Inline JS for admin login / passkey pages (same as the original TS Worker).
pub const WEBAUTHN_CLIENT_JS: &str = r#"
const b64u = {
  dec: s => {
    s = s.replace(/-/g,'+').replace(/_/g,'/');
    while (s.length % 4) s += '=';
    return Uint8Array.from(atob(s), c => c.charCodeAt(0)).buffer;
  },
  enc: buf => btoa(String.fromCharCode(...new Uint8Array(buf)))
    .replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,''),
};

async function postJSON(url, body) {
  const r = await fetch(url, {
    method: 'POST',
    headers: body ? {'content-type': 'application/json'} : {},
    body: body ? JSON.stringify(body) : undefined,
    credentials: 'same-origin',
  });
  if (!r.ok) throw new Error('HTTP ' + r.status + ': ' + (await r.text()));
  const ct = r.headers.get('content-type') || '';
  return ct.includes('application/json') ? r.json() : null;
}

async function pkRegister(label) {
  const opts = await postJSON('/admin/passkeys/register/options');
  opts.challenge = b64u.dec(opts.challenge);
  opts.user.id = b64u.dec(opts.user.id);
  if (opts.excludeCredentials) {
    opts.excludeCredentials = opts.excludeCredentials.map(c => ({...c, id: b64u.dec(c.id)}));
  }
  const cred = await navigator.credentials.create({ publicKey: opts });
  const resp = {
    id: cred.id,
    rawId: b64u.enc(cred.rawId),
    type: cred.type,
    response: {
      attestationObject: b64u.enc(cred.response.attestationObject),
      clientDataJSON: b64u.enc(cred.response.clientDataJSON),
      transports: cred.response.getTransports ? cred.response.getTransports() : [],
    },
    clientExtensionResults: cred.getClientExtensionResults ? cred.getClientExtensionResults() : {},
    authenticatorAttachment: cred.authenticatorAttachment || null,
  };
  await postJSON('/admin/passkeys/register/verify', { label, response: resp });
  location.reload();
}

async function pkLogin() {
  const opts = await postJSON('/admin/login/passkey/options');
  opts.challenge = b64u.dec(opts.challenge);
  if (opts.allowCredentials) {
    opts.allowCredentials = opts.allowCredentials.map(c => ({...c, id: b64u.dec(c.id)}));
  }
  const cred = await navigator.credentials.get({ publicKey: opts });
  const resp = {
    id: cred.id,
    rawId: b64u.enc(cred.rawId),
    type: cred.type,
    response: {
      authenticatorData: b64u.enc(cred.response.authenticatorData),
      clientDataJSON: b64u.enc(cred.response.clientDataJSON),
      signature: b64u.enc(cred.response.signature),
      userHandle: cred.response.userHandle ? b64u.enc(cred.response.userHandle) : null,
    },
    clientExtensionResults: cred.getClientExtensionResults ? cred.getClientExtensionResults() : {},
    authenticatorAttachment: cred.authenticatorAttachment || null,
  };
  await postJSON('/admin/login/passkey/verify', resp);
  location.href = '/admin';
}

window.pkRegister = pkRegister;
window.pkLogin = pkLogin;
"#;

pub struct LayoutOpts<'a> {
    pub title: &'a str,
    pub site_title: &'a str,
    pub site_url: &'a str,
    pub description: Option<&'a str>,
    pub og_image: Option<String>,
    pub canonical: Option<String>,
    pub og_type: &'a str,
}

pub fn layout(opts: LayoutOpts<'_>, body: &str) -> String {
    let desc = opts.description.unwrap_or("");
    let mut head = String::new();
    if !desc.is_empty() {
        head.push_str(&format!(
            "<meta name=\"description\" content=\"{}\" />\n",
            escape_html(desc)
        ));
    }
    if let Some(c) = &opts.canonical {
        head.push_str(&format!(
            "<link rel=\"canonical\" href=\"{}\" />\n",
            escape_html(c)
        ));
    }
    head.push_str(&format!(
        r#"<link rel="alternate" type="application/rss+xml" title="{}" href="/feed.xml" />"#,
        escape_html(opts.site_title)
    ));
    let og_image = opts.og_image.as_deref().unwrap_or("");
    let twitter = if og_image.is_empty() {
        "summary"
    } else {
        "summary_large_image"
    };
    format!(
        r#"<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>{title}</title>
    {head}
    <link rel="preconnect" href="https://fonts.googleapis.com" />
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />
    <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Courier+Prime:ital,wght@0,400;0,700;1,400;1,700&display=swap" />
    <meta property="og:type" content="{og_type}" />
    <meta property="og:title" content="{title}" />
    <meta property="og:site_name" content="{site_title}" />
    {og_desc}{og_url}{og_img}
    <meta name="twitter:card" content="{twitter}" />
    <style>{style}</style>
  </head>
  <body>
    <div class="paper">
      <header>
        <h1><a href="/">{site_title}</a></h1>
        <nav>
          <a href="/subscribe">subscribe</a>
          <a href="/feed.xml">rss</a>
        </nav>
      </header>
      <main>{body}</main>
      <footer>
        <a href="/">home</a> · <a href="/feed.xml">rss</a> ·
        <a href="/subscribe">subscribe</a>
      </footer>
    </div>
  </body>
</html>"#,
        title = escape_html(opts.title),
        site_title = escape_html(opts.site_title),
        og_type = escape_html(opts.og_type),
        og_desc = if desc.is_empty() {
            String::new()
        } else {
            format!(
                "<meta property=\"og:description\" content=\"{}\" />\n",
                escape_html(desc)
            )
        },
        og_url = match &opts.canonical {
            Some(c) => format!(
                "<meta property=\"og:url\" content=\"{}\" />\n",
                escape_html(c)
            ),
            None => String::new(),
        },
        og_img = if og_image.is_empty() {
            String::new()
        } else {
            format!(
                "<meta property=\"og:image\" content=\"{}\" />\n",
                escape_html(og_image)
            )
        },
        style = STYLE,
        twitter = twitter,
        head = head,
        body = body,
    )
}

pub fn post_fragment(
    site_url: &str,
    post: &Post,
    images: &[PostImage],
    logged_in: bool,
    current: bool,
    reply_count: i64,
) -> String {
    let dt = format_iso8601(post.created_at);
    let human = format_rfc1123(post.created_at);
    let yt = extract_youtube_ref(&post.body);
    let cls = if current { "post current" } else { "post" };
    let mut html = format!(r#"<article class="{cls}" id="post-{id}">"#, id = post.id);
    if !post.body.is_empty() {
        html.push_str(&format!(
            r#"<div class="postbody">{}</div>"#,
            linkify_body(&post.body)
        ));
    }
    if let Some(yt) = &yt {
        html.push_str(&format!(
            r#"<div class="yt"><iframe src="{src}" title="YouTube video" loading="lazy" allow="accelerometer; encrypted-media; gyroscope; picture-in-picture; web-share" allowfullscreen referrerpolicy="strict-origin-when-cross-origin"></iframe></div>"#,
            src = escape_html(&youtube_embed_src(yt))
        ));
    }
    if !images.is_empty() {
        html.push_str(r#"<div class="images">"#);
        for img in images {
            let w = img
                .width
                .map(|n| format!(" width=\"{n}\""))
                .unwrap_or_default();
            let h = img
                .height
                .map(|n| format!(" height=\"{n}\""))
                .unwrap_or_default();
            html.push_str(&format!(
                r#"<span class="clipped"><img src="{src}"{w}{h} alt="{alt}" loading="lazy" /></span>"#,
                src = escape_html(&img_url(site_url, &img.r2_key)),
                alt = escape_html(img.alt.as_deref().unwrap_or("")),
            ));
        }
        html.push_str("</div>");
    }
    html.push_str(r#"<div class="meta">"#);
    if reply_count > 0 {
        let word = if reply_count == 1 { "reply" } else { "replies" };
        html.push_str(&format!(
            r#"<a class="replies" href="/post/{id}">→ {n} {word}</a>"#,
            id = post.id,
            n = reply_count
        ));
    }
    html.push_str(&format!(
        r#"<span class="actions"><a class="time" href="/post/{id}"><time datetime="{dt}">{human}</time></a>"#,
        id = post.id,
        dt = escape_html(&dt),
        human = escape_html(&human),
    ));
    if logged_in {
        html.push_str(&format!(
            r#"<span class="sep">|</span>
              <a href="/admin?reply_to={id}">reply</a>
              <span class="sep">|</span>
              <a href="/admin/posts/{id}/edit">edit</a>
              <span class="sep">|</span>
              <form method="post" action="/admin/posts/{id}/delete" onsubmit="return confirm('delete this post?')">
                <button type="submit">delete</button>
              </form>"#,
            id = post.id
        ));
    }
    html.push_str("</span></div></article>");
    html
}

pub fn index_view(
    site_title: &str,
    site_url: &str,
    posts: &[Post],
    images_by_post: &[(i64, Vec<PostImage>)],
    logged_in: bool,
    reply_counts: &[(i64, i64)],
) -> String {
    let mut body = String::new();
    if logged_in {
        body.push_str(r#"<p class="adminbar"><a href="/admin">+ post</a></p>"#);
    }
    if posts.is_empty() {
        body.push_str(r#"<p class="empty">No posts yet.</p>"#);
    } else {
        for p in posts {
            let images = images_by_post
                .iter()
                .find(|(id, _)| *id == p.id)
                .map(|(_, v)| v.as_slice())
                .unwrap_or(&[]);
            let replies = reply_counts
                .iter()
                .find(|(id, _)| *id == p.id)
                .map(|(_, n)| *n)
                .unwrap_or(0);
            body.push_str(&post_fragment(
                site_url, p, images, logged_in, false, replies,
            ));
        }
    }
    layout(
        LayoutOpts {
            title: site_title,
            site_title,
            site_url,
            description: None,
            og_image: None,
            canonical: Some(site_url.to_string()),
            og_type: "website",
        },
        &body,
    )
}

pub fn post_view(
    site_title: &str,
    site_url: &str,
    post: &Post,
    thread_posts: &[Post],
    images_by_post: &[(i64, Vec<PostImage>)],
    logged_in: bool,
    head_id: i64,
) -> String {
    let yt = extract_youtube_ref(&post.body);
    let own_images = images_by_post
        .iter()
        .find(|(id, _)| *id == post.id)
        .map(|(_, v)| v.as_slice())
        .unwrap_or(&[]);
    let og_image = own_images
        .first()
        .map(|i| img_url(site_url, &i.r2_key))
        .or_else(|| yt.as_ref().map(youtube_thumbnail_url));
    let desc = if post.body.is_empty() {
        None
    } else {
        Some(truncate(&post.body, 200))
    };
    let title_text = if post.body.is_empty() {
        "image".to_string()
    } else {
        truncate(&post.body, 60)
    };
    let title = format!("{title_text} — {site_title}");
    let canonical = format!("{}/post/{}", site_url.trim_end_matches('/'), post.id);
    let mut body = String::new();
    if head_id != post.id {
        body.push_str(&format!(
            r#"<p class="thread-top"><a href="/post/{head_id}">↑ top of thread</a></p>"#
        ));
    }
    for p in thread_posts {
        let images = images_by_post
            .iter()
            .find(|(id, _)| *id == p.id)
            .map(|(_, v)| v.as_slice())
            .unwrap_or(&[]);
        body.push_str(&post_fragment(
            site_url,
            p,
            images,
            logged_in,
            p.id == post.id,
            0,
        ));
    }
    layout(
        LayoutOpts {
            title: &title,
            site_title,
            site_url,
            description: desc.as_deref(),
            og_image,
            canonical: Some(canonical),
            og_type: "article",
        },
        &body,
    )
}

pub fn simple_page(site_title: &str, site_url: &str, title: &str, body: &str) -> String {
    let full = format!("{title} — {site_title}");
    layout(
        LayoutOpts {
            title: &full,
            site_title,
            site_url,
            description: None,
            og_image: None,
            canonical: None,
            og_type: "website",
        },
        body,
    )
}

pub fn rss_feed(
    site_title: &str,
    site_url: &str,
    posts: &[Post],
    images_by_post: &[(i64, Vec<PostImage>)],
) -> String {
    let mut items = String::new();
    for p in posts {
        let imgs = images_by_post
            .iter()
            .find(|(id, _)| *id == p.id)
            .map(|(_, v)| v.as_slice())
            .unwrap_or(&[]);
        let body = escape_html(&p.body).replace('\n', "<br>");
        let mut img_html = String::new();
        for i in imgs {
            img_html.push_str(&format!(
                r#"<p><img src="{}" alt="{}"></p>"#,
                escape_html(&img_url(site_url, &i.r2_key)),
                escape_html(i.alt.as_deref().unwrap_or(""))
            ));
        }
        let description = format!(
            "{}{}",
            if p.body.is_empty() {
                String::new()
            } else {
                format!("<p>{body}</p>")
            },
            img_html
        );
        let link = format!("{}/post/{}", site_url.trim_end_matches('/'), p.id);
        let title = if !p.body.is_empty() {
            truncate(&p.body, 80)
        } else if !imgs.is_empty() {
            "(image)".into()
        } else {
            link.clone()
        };
        items.push_str(&format!(
            "    <item>
      <title>{}</title>
      <link>{}</link>
      <guid isPermaLink=\"true\">{}</guid>
      <pubDate>{}</pubDate>
      <description><![CDATA[{description}]]></description>
    </item>\n",
            escape_html(&title),
            escape_html(&link),
            escape_html(&link),
            format_rfc1123(p.created_at),
        ));
    }
    let last_build = if let Some(p) = posts.first() {
        format_rfc1123(p.created_at)
    } else {
        format_rfc1123(0)
    };
    format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom">
  <channel>
    <title>{title}</title>
    <link>{link}</link>
    <description>{title}</description>
    <atom:link href="{feed}" rel="self" type="application/rss+xml"/>
    <lastBuildDate>{last_build}</lastBuildDate>
{items}  </channel>
</rss>
"#,
        title = escape_html(site_title),
        link = escape_html(site_url),
        feed = escape_html(&format!("{}/feed.xml", site_url.trim_end_matches('/'))),
    )
}

pub fn subscribe_form(site_title: &str, site_url: &str) -> String {
    simple_page(
        site_title,
        site_url,
        "subscribe",
        r#"<p>Email subscriptions aren't built yet — but the RSS feed is.
          Drop your address and I'll let you know when there's an email
          option too.</p>
        <form method="post" action="/subscribe" class="row">
          <input type="email" name="email" placeholder="you@example.com" required>
          <button type="submit">register interest</button>
        </form>
        <p>Or grab the <a href="/feed.xml">RSS feed</a> right now.</p>"#,
    )
}

pub fn subscribe_thanks(site_title: &str, site_url: &str) -> String {
    simple_page(
        site_title,
        site_url,
        "thanks",
        r#"<p class="ok">Got it — you're on the list. I'll reach out
          when email subscriptions are live.</p>
        <p><a href="/">← back</a></p>"#,
    )
}

pub fn login_page(site_title: &str, site_url: &str, bootstrap: bool, err: bool) -> String {
    let inner = if bootstrap {
        format!(
            r#"<p class="ok">No passkey registered yet. Sign in with the bootstrap password to register one.</p>
            <form method="post" action="/admin/login">
              <p><input type="password" name="password" placeholder="password" autofocus required></p>
              {}
              <p><button type="submit">log in</button></p>
            </form>"#,
            if err {
                r#"<p class="err">incorrect password</p>"#
            } else {
                ""
            }
        )
    } else {
        r#"<p>
              <button type="button" onclick="pkLogin().catch(e=>document.getElementById('pk-err').textContent=String(e))">
                log in with passkey
              </button>
              <span id="pk-err" class="err"></span>
            </p>"#
            .to_string()
    };
    let body = format!("{inner}<script>{WEBAUTHN_CLIENT_JS}</script>");
    simple_page(site_title, site_url, "login", &body)
}

pub fn passkeys_page(
    site_title: &str,
    site_url: &str,
    creds: &[(i64, String, i64)],
    bootstrap: bool,
) -> String {
    let mut inner = String::new();
    if bootstrap {
        inner.push_str(r#"<p class="ok">You're in. Register a passkey now to lock down login — the bootstrap password becomes inactive after the first one is added.</p>"#);
    }
    inner.push_str("<h2>passkeys</h2>");
    if creds.is_empty() {
        inner.push_str(r#"<p class="empty">none registered.</p>"#);
    } else {
        inner.push_str("<ul>");
        for (id, label, created) in creds {
            inner.push_str(&format!(
                r#"<li><strong>{}</strong><span class="meta"> — added {}</span>
                  <form method="post" action="/admin/passkeys/{id}/delete" style="display:inline" onsubmit="return confirm('delete passkey?')">
                    <button type="submit">delete</button>
                  </form></li>"#,
                escape_html(label),
                escape_html(&format_rfc1123(*created)),
            ));
        }
        inner.push_str("</ul>");
    }
    inner.push_str(&format!(
        r#"<h3>add a passkey</h3>
        <form onsubmit="event.preventDefault(); pkRegister(this.label.value).catch(e=>document.getElementById('pk-err').textContent=String(e))" class="row">
          <input type="text" name="label" placeholder="e.g. laptop" required>
          <button type="submit">register</button>
        </form>
        <p id="pk-err" class="err"></p>
        <p><a href="/admin">← back to admin</a></p>
        <script>{WEBAUTHN_CLIENT_JS}</script>"#
    ));
    simple_page(site_title, site_url, "passkeys", &inner)
}

pub fn admin_compose(
    site_title: &str,
    site_url: &str,
    reply_to: Option<&Post>,
    interest_count: i64,
) -> String {
    let mut inner = String::new();
    if interest_count >= 10 {
        inner.push_str(&format!(
            r#"<p class="interest-banner">📬 {interest_count} people have registered interest in email subscriptions — time to wire that up.</p>"#
        ));
    }
    if let Some(p) = reply_to {
        let snippet = truncate(&p.body, 80);
        inner.push_str(&format!(
            r#"<p class="reply-ctx">↳ replying to <a href="/post/{id}">«{snippet}»</a> · <a href="/admin">cancel</a></p>"#,
            id = p.id,
            snippet = escape_html(&snippet),
        ));
    }
    let hidden = reply_to
        .map(|p| format!(r#"<input type="hidden" name="parent_id" value="{}">"#, p.id))
        .unwrap_or_default();
    let verb = if reply_to.is_some() { "reply" } else { "post" };
    inner.push_str(&format!(
        r#"<form method="post" action="/admin/posts" enctype="multipart/form-data">
        {hidden}
        <p><textarea name="body" maxlength="{POST_MAX_CHARS}" autofocus
          placeholder="say something (max {POST_MAX_CHARS} chars), or just attach an image"
          oninput="var r={POST_MAX_CHARS}-this.value.length;ycnt.textContent=r;ycnt.className=r<20?'warn':''"
          onkeydown="if((event.metaKey||event.ctrlKey)&&event.key==='Enter'){{event.preventDefault();this.form.requestSubmit()}}"></textarea></p>
        <p><input type="file" name="image" accept="image/*" multiple></p>
        <p>
          <button type="submit" class="btn">{verb}</button>
          <span class="counter"><output id="ycnt">{POST_MAX_CHARS}</output> left</span>
        </p>
      </form>
      <p class="admin-bottom row">
        <a href="/admin/passkeys">passkeys</a>
        <form method="post" action="/admin/logout" style="display:inline">
          <button type="submit">log out</button>
        </form>
      </p>"#
    ));
    simple_page(site_title, site_url, "admin", &inner)
}

pub fn edit_page(site_title: &str, site_url: &str, post: &Post) -> String {
    let left = POST_MAX_CHARS.saturating_sub(utf16_len(&post.body));
    let warn = if left < 20 { "warn" } else { "" };
    let id = post.id;
    let escaped = escape_html(&post.body);
    let body = format!(
        r#"<h2>edit post #{id}</h2>
        <form method="post" action="/admin/posts/{id}/edit">
          <p><textarea name="body" maxlength="{POST_MAX_CHARS}"
            oninput="var r={POST_MAX_CHARS}-this.value.length;ycnt.textContent=r;ycnt.className=r<20?'warn':''"
            onkeydown="if((event.metaKey||event.ctrlKey)&&event.key==='Enter'){{event.preventDefault();this.form.requestSubmit()}}">{escaped}</textarea></p>
          <p>
            <button type="submit">save</button>
            <a href="/post/{id}">cancel</a>
            <span class="counter"><output id="ycnt" class="{warn}">{left}</output> left</span>
          </p>
        </form>"#,
    );
    simple_page(site_title, site_url, "edit", &body)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_and_linkifies() {
        assert_eq!(escape_html("<a&b>"), "&lt;a&amp;b&gt;");
        let html = linkify_body("see https://example.com.");
        assert!(html.contains(r#"href="https://example.com""#), "{html}");
        assert!(!html.contains(".</a>"), "{html}");
        let code = linkify_body("use `x` here");
        assert_eq!(code, "use <code>x</code> here");
        let fence = linkify_body("```\nls\n```");
        assert!(fence.contains("<pre><code>ls</code></pre>"), "{fence}");
    }

    #[test]
    fn youtube_watch_and_short() {
        let a = extract_youtube_ref("watch https://www.youtube.com/watch?v=dQw4w9wgGcQ now");
        assert_eq!(a.unwrap().id, "dQw4w9wgGcQ");
        let b = extract_youtube_ref("https://youtu.be/dQw4w9wgGcQ?t=30s");
        assert_eq!(b.unwrap().start, Some(30));
    }

    #[test]
    fn rfc1123_epoch() {
        assert_eq!(format_rfc1123(0), "Thu, 01 Jan 1970 00:00:00 GMT");
    }

    #[test]
    fn email_sanity() {
        assert!(is_valid_email("a@b.co"));
        assert!(!is_valid_email("nope"));
        assert!(!is_valid_email("a@b"));
    }
}
