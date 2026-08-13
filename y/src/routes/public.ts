import { Hono } from "hono";
import { getCookie } from "hono/cookie";
import { SESSION_COOKIE, verifySessionCookie } from "../auth";
import {
  getPost,
  getThread,
  imagesForPosts,
  listAllPosts,
  listHeadPosts,
  totalRepliesByHead,
} from "../db";
import { indexView, postView, rssFeed } from "../views";

export const publicRoutes = new Hono<{ Bindings: Env }>();

const PAGE_SIZE = 50;

publicRoutes.get("/", async (c) => {
  const before = c.req.query("before");
  const beforeTs = before ? Number(before) : undefined;
  const [posts, loggedIn] = await Promise.all([
    listHeadPosts(
      c.env.DB,
      PAGE_SIZE,
      Number.isFinite(beforeTs) ? beforeTs : undefined,
    ),
    verifySessionCookie(
      c.env.SESSION_SECRET,
      getCookie(c, SESSION_COOKIE),
      Math.floor(Date.now() / 1000),
    ),
  ]);
  const [images, replyCounts] = await Promise.all([
    imagesForPosts(
      c.env.DB,
      posts.map((p) => p.id),
    ),
    totalRepliesByHead(
      c.env.DB,
      posts.map((p) => p.id),
    ),
  ]);
  return c.html(
    indexView(c.env.SITE_TITLE, c.env.SITE_URL, posts, images, {
      loggedIn,
      replyCounts,
    }),
  );
});

publicRoutes.get("/post/:id{[0-9]+}", async (c) => {
  const id = Number(c.req.param("id"));
  const [post, loggedIn] = await Promise.all([
    getPost(c.env.DB, id),
    verifySessionCookie(
      c.env.SESSION_SECRET,
      getCookie(c, SESSION_COOKIE),
      Math.floor(Date.now() / 1000),
    ),
  ]);
  if (!post) return c.notFound();

  const thread = await getThread(c.env.DB, id);
  const threadPosts = thread?.posts ?? [post];
  const images = await imagesForPosts(
    c.env.DB,
    threadPosts.map((p) => p.id),
  );
  return c.html(
    postView(c.env.SITE_TITLE, c.env.SITE_URL, post, threadPosts, images, {
      loggedIn,
      headId: thread?.head.id ?? post.id,
    }),
  );
});

publicRoutes.get("/feed.xml", async (c) => {
  const posts = await listAllPosts(c.env.DB, PAGE_SIZE);
  const images = await imagesForPosts(
    c.env.DB,
    posts.map((p) => p.id),
  );
  const body = rssFeed(c.env.SITE_TITLE, c.env.SITE_URL, posts, images);
  return c.body(body, 200, {
    "content-type": "application/rss+xml; charset=utf-8",
    "cache-control": "public, max-age=300",
  });
});

publicRoutes.get("/img/:key{.+}", async (c) => {
  const key = c.req.param("key");
  const obj = await c.env.IMAGES.get(key);
  if (!obj) return c.notFound();
  const headers = new Headers();
  obj.writeHttpMetadata(headers);
  headers.set("etag", obj.httpEtag);
  headers.set("cache-control", "public, max-age=31536000, immutable");
  return new Response(obj.body, { headers });
});
