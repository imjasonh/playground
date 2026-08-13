import { html, raw } from "hono/html";
import type { HtmlEscapedString } from "hono/utils/html";
import type { Post, PostImage } from "./db";
import {
  escapeHtml,
  extractYouTubeRef,
  formatDate,
  formatHuman,
  imgUrl,
  linkifyBody,
  truncate,
  youtubeEmbedSrc,
  youtubeThumbnailUrl,
} from "./util";

type Html = HtmlEscapedString | Promise<HtmlEscapedString>;

const STYLE = `
  :root { color-scheme: light; }
  body {
    font: 17px/1.55 'Courier Prime', 'American Typewriter', 'Courier New', Courier, monospace;
    margin: 0;
    padding: 2.5rem 1rem;
    min-height: 100vh;
    background: #bfb39a; /* desk surface */
    color: #1a1410;
  }
  .paper {
    max-width: 640px;
    margin: 0 auto;
    background: #fdfaf2; /* sheet of paper */
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
      /* anchor to the photo's left-edge midpoint, independent of the
         photo's display size so it lines up the same on any viewport */
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
`;

interface LayoutOpts {
  title: string;
  siteTitle: string;
  siteUrl: string;
  description?: string;
  ogImage?: string;
  canonical?: string;
  ogType?: "website" | "article";
}

export function layout(opts: LayoutOpts, body: Html): Html {
  const desc = opts.description ?? "";
  return html`<!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
        <title>${opts.title}</title>
        ${desc ? html`<meta name="description" content="${desc}" />` : ""}
        ${opts.canonical
          ? html`<link rel="canonical" href="${opts.canonical}" />`
          : ""}
        <link
          rel="alternate"
          type="application/rss+xml"
          title="${opts.siteTitle}"
          href="/feed.xml"
        />
        <link rel="preconnect" href="https://fonts.googleapis.com" />
        <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />
        <link
          rel="stylesheet"
          href="https://fonts.googleapis.com/css2?family=Courier+Prime:ital,wght@0,400;0,700;1,400;1,700&display=swap"
        />
        <meta property="og:type" content="${opts.ogType ?? "website"}" />
        <meta property="og:title" content="${opts.title}" />
        <meta property="og:site_name" content="${opts.siteTitle}" />
        ${desc
          ? html`<meta property="og:description" content="${desc}" />`
          : ""}
        ${opts.canonical
          ? html`<meta property="og:url" content="${opts.canonical}" />`
          : ""}
        ${opts.ogImage
          ? html`<meta property="og:image" content="${opts.ogImage}" />`
          : ""}
        <meta
          name="twitter:card"
          content="${opts.ogImage ? "summary_large_image" : "summary"}"
        />
        <style>
          ${raw(STYLE)}
        </style>
      </head>
      <body>
        <div class="paper">
          <header>
            <h1><a href="/">${opts.siteTitle}</a></h1>
            <nav>
              <a href="/subscribe">subscribe</a>
              <a href="/feed.xml">rss</a>
            </nav>
          </header>
          <main>${body}</main>
          <footer>
            <a href="/">home</a> · <a href="/feed.xml">rss</a> ·
            <a href="/subscribe">subscribe</a>
          </footer>
        </div>
      </body>
    </html>`;
}

export function postFragment(
  siteUrl: string,
  post: Post,
  images: PostImage[],
  opts: {
    loggedIn?: boolean;
    current?: boolean;
    replyCount?: number;
  } = {},
): Html {
  const dt = formatDate(post.created_at);
  const human = formatHuman(post.created_at);
  const yt = extractYouTubeRef(post.body);
  const cls = opts.current ? "post current" : "post";
  return html`<article class="${cls}" id="post-${post.id}">
    ${post.body
      ? html`<div class="postbody">${linkifyBody(post.body)}</div>`
      : ""}
    ${yt
      ? html`<div class="yt">
          <iframe
            src="${youtubeEmbedSrc(yt)}"
            title="YouTube video"
            loading="lazy"
            allow="accelerometer; encrypted-media; gyroscope; picture-in-picture; web-share"
            allowfullscreen
            referrerpolicy="strict-origin-when-cross-origin"
          ></iframe>
        </div>`
      : ""}
    ${images.length > 0
      ? html`<div class="images">
          ${images.map(
            (img) =>
              html`<span class="clipped">
                <img
                  src="${imgUrl(siteUrl, img.r2_key)}"
                  ${img.width ? html`width="${img.width}"` : ""}
                  ${img.height ? html`height="${img.height}"` : ""}
                  alt="${img.alt ?? ""}"
                  loading="lazy"
                />
              </span>`,
          )}
        </div>`
      : ""}
    <div class="meta">
      ${opts.replyCount && opts.replyCount > 0
        ? html`<a class="replies" href="/post/${post.id}"
            >→ ${opts.replyCount}
            ${opts.replyCount === 1 ? "reply" : "replies"}</a
          >`
        : ""}
      <span class="actions">
        <a class="time" href="/post/${post.id}"
          ><time datetime="${dt}">${human}</time></a
        >
        ${opts.loggedIn
          ? html`<span class="sep">|</span>
              <a href="/admin?reply_to=${post.id}">reply</a>
              <span class="sep">|</span>
              <a href="/admin/posts/${post.id}/edit">edit</a>
              <span class="sep">|</span>
              <form
                method="post"
                action="/admin/posts/${post.id}/delete"
                onsubmit="return confirm('delete this post?')"
              >
                <button type="submit">delete</button>
              </form>`
          : ""}
      </span>
    </div>
  </article>`;
}

export function indexView(
  siteTitle: string,
  siteUrl: string,
  posts: Post[],
  imagesByPost: Map<number, PostImage[]>,
  opts: { loggedIn?: boolean; replyCounts?: Map<number, number> } = {},
): Html {
  const adminBar = opts.loggedIn
    ? html`<p class="adminbar"><a href="/admin">+ post</a></p>`
    : "";
  const body =
    posts.length === 0
      ? html`${adminBar}
          <p class="empty">No posts yet.</p>`
      : html`${adminBar}${posts.map((p) =>
          postFragment(siteUrl, p, imagesByPost.get(p.id) ?? [], {
            loggedIn: opts.loggedIn,
            replyCount: opts.replyCounts?.get(p.id) ?? 0,
          }),
        )}`;
  return layout(
    {
      title: siteTitle,
      siteTitle,
      siteUrl,
      canonical: siteUrl,
      ogType: "website",
    },
    body,
  );
}

export function postView(
  siteTitle: string,
  siteUrl: string,
  post: Post,
  threadPosts: Post[],
  imagesByPost: Map<number, PostImage[]>,
  opts: { loggedIn?: boolean; headId?: number } = {},
): Html {
  const yt = extractYouTubeRef(post.body);
  const ownImages = imagesByPost.get(post.id) ?? [];
  const ogImage = ownImages[0]
    ? imgUrl(siteUrl, ownImages[0].r2_key)
    : yt
      ? youtubeThumbnailUrl(yt)
      : undefined;
  const desc = post.body ? truncate(post.body, 200) : undefined;
  const titleText = post.body ? truncate(post.body, 60) : "image";
  const canonical = `${siteUrl.replace(/\/$/, "")}/post/${post.id}`;
  const headId = opts.headId ?? post.id;
  const showTopLink = headId !== post.id;
  return layout(
    {
      title: `${titleText} — ${siteTitle}`,
      siteTitle,
      siteUrl,
      description: desc,
      ogImage,
      canonical,
      ogType: "article",
    },
    html`${showTopLink
      ? html`<p class="thread-top">
          <a href="/post/${headId}">↑ top of thread</a>
        </p>`
      : ""}
    ${threadPosts.map((p) =>
      postFragment(siteUrl, p, imagesByPost.get(p.id) ?? [], {
        loggedIn: opts.loggedIn,
        current: p.id === post.id,
      }),
    )}`,
  );
}

export function simplePage(
  siteTitle: string,
  siteUrl: string,
  title: string,
  bodyHtml: Html,
): Html {
  return layout(
    { title: `${title} — ${siteTitle}`, siteTitle, siteUrl },
    bodyHtml,
  );
}

export function rssFeed(
  siteTitle: string,
  siteUrl: string,
  posts: Post[],
  imagesByPost: Map<number, PostImage[]>,
): string {
  const items = posts.map((p) => {
    const imgs = imagesByPost.get(p.id) ?? [];
    const body = escapeHtml(p.body).replace(/\n/g, "<br>");
    const imgHtml = imgs
      .map(
        (i) =>
          `<p><img src="${escapeHtml(imgUrl(siteUrl, i.r2_key))}" alt="${escapeHtml(i.alt ?? "")}"></p>`,
      )
      .join("");
    const description = `${p.body ? `<p>${body}</p>` : ""}${imgHtml}`;
    const link = `${siteUrl.replace(/\/$/, "")}/post/${p.id}`;
    const title = p.body
      ? truncate(p.body, 80)
      : imgs.length > 0
        ? "(image)"
        : link;
    return `    <item>
      <title>${escapeHtml(title)}</title>
      <link>${escapeHtml(link)}</link>
      <guid isPermaLink="true">${escapeHtml(link)}</guid>
      <pubDate>${new Date(p.created_at * 1000).toUTCString()}</pubDate>
      <description><![CDATA[${description}]]></description>
    </item>`;
  });
  const lastBuild =
    posts.length > 0
      ? new Date(posts[0].created_at * 1000).toUTCString()
      : new Date().toUTCString();
  return `<?xml version="1.0" encoding="UTF-8"?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom">
  <channel>
    <title>${escapeHtml(siteTitle)}</title>
    <link>${escapeHtml(siteUrl)}</link>
    <description>${escapeHtml(siteTitle)}</description>
    <atom:link href="${escapeHtml(siteUrl.replace(/\/$/, ""))}/feed.xml" rel="self" type="application/rss+xml"/>
    <lastBuildDate>${lastBuild}</lastBuildDate>
${items.join("\n")}
  </channel>
</rss>
`;
}
