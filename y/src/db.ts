export interface Post {
  id: number;
  body: string;
  created_at: number;
  parent_id: number | null;
}

export interface PostImage {
  id: number;
  post_id: number;
  r2_key: string;
  content_type: string;
  width: number | null;
  height: number | null;
  alt: string | null;
  ordinal: number;
}

export interface Subscriber {
  id: number;
  email: string;
  status: "pending" | "confirmed" | "unsubscribed";
  token: string | null;
  created_at: number;
  confirmed_at: number | null;
}

const POST_COLS = "id, body, created_at, parent_id";

// Timeline = head posts (no parent) only, newest first.
export async function listHeadPosts(
  db: D1Database,
  limit: number,
  before?: number,
): Promise<Post[]> {
  const stmt = before
    ? db
        .prepare(
          `SELECT ${POST_COLS} FROM posts
           WHERE parent_id IS NULL AND created_at < ?1
           ORDER BY created_at DESC LIMIT ?2`,
        )
        .bind(before, limit)
    : db
        .prepare(
          `SELECT ${POST_COLS} FROM posts
           WHERE parent_id IS NULL
           ORDER BY created_at DESC LIMIT ?1`,
        )
        .bind(limit);
  const { results } = await stmt.all<Post>();
  return results;
}

// All posts, newest first — used by RSS so subscribers see everything.
export async function listAllPosts(
  db: D1Database,
  limit: number,
): Promise<Post[]> {
  const { results } = await db
    .prepare(
      `SELECT ${POST_COLS} FROM posts ORDER BY created_at DESC LIMIT ?1`,
    )
    .bind(limit)
    .all<Post>();
  return results;
}

export async function getPost(
  db: D1Database,
  id: number,
): Promise<Post | null> {
  return await db
    .prepare(`SELECT ${POST_COLS} FROM posts WHERE id = ?1`)
    .bind(id)
    .first<Post>();
}

// Map head-post id -> number of replies anywhere in its subtree. Walks
// the parent chain in SQL via a recursive CTE.
export async function totalRepliesByHead(
  db: D1Database,
  headIds: number[],
): Promise<Map<number, number>> {
  const out = new Map<number, number>(headIds.map((id) => [id, 0]));
  if (headIds.length === 0) return out;
  const placeholders = headIds.map(() => "?").join(",");
  const { results } = await db
    .prepare(
      `WITH RECURSIVE chain(id, head) AS (
         SELECT id, id FROM posts WHERE id IN (${placeholders})
         UNION ALL
         SELECT p.id, c.head FROM posts p JOIN chain c ON p.parent_id = c.id
       )
       SELECT head, COUNT(*) - 1 AS reply_count FROM chain GROUP BY head`,
    )
    .bind(...headIds)
    .all<{ head: number; reply_count: number }>();
  for (const r of results) out.set(r.head, r.reply_count);
  return out;
}

// Get the full thread that includes `id`: walks up to the head, then
// down through all descendants. Posts are returned in chronological
// order. Branching is supported but rendered linearly by ordering on
// created_at.
export async function getThread(
  db: D1Database,
  id: number,
): Promise<{ head: Post; posts: Post[] } | null> {
  const head = await findHead(db, id);
  if (!head) return null;
  const { results } = await db
    .prepare(
      `WITH RECURSIVE thread AS (
         SELECT ${POST_COLS} FROM posts WHERE id = ?1
         UNION ALL
         SELECT p.id, p.body, p.created_at, p.parent_id
           FROM posts p JOIN thread t ON p.parent_id = t.id
       )
       SELECT * FROM thread ORDER BY created_at ASC`,
    )
    .bind(head.id)
    .all<Post>();
  return { head, posts: results };
}

async function findHead(
  db: D1Database,
  id: number,
): Promise<Post | null> {
  const row = await db
    .prepare(
      `WITH RECURSIVE up AS (
         SELECT ${POST_COLS} FROM posts WHERE id = ?1
         UNION ALL
         SELECT p.id, p.body, p.created_at, p.parent_id
           FROM posts p JOIN up u ON p.id = u.parent_id
       )
       SELECT * FROM up WHERE parent_id IS NULL LIMIT 1`,
    )
    .bind(id)
    .first<Post>();
  return row;
}

export async function imagesForPosts(
  db: D1Database,
  postIds: number[],
): Promise<Map<number, PostImage[]>> {
  const out = new Map<number, PostImage[]>();
  if (postIds.length === 0) return out;
  const placeholders = postIds.map(() => "?").join(",");
  const { results } = await db
    .prepare(
      `SELECT id, post_id, r2_key, content_type, width, height, alt, ordinal
         FROM post_images
        WHERE post_id IN (${placeholders})
        ORDER BY post_id, ordinal`,
    )
    .bind(...postIds)
    .all<PostImage>();
  for (const img of results) {
    const arr = out.get(img.post_id) ?? [];
    arr.push(img);
    out.set(img.post_id, arr);
  }
  return out;
}

export async function imagesForPost(
  db: D1Database,
  postId: number,
): Promise<PostImage[]> {
  const m = await imagesForPosts(db, [postId]);
  return m.get(postId) ?? [];
}

export async function insertPost(
  db: D1Database,
  body: string,
  createdAt: number,
  parentId: number | null,
): Promise<number> {
  const res = await db
    .prepare(
      "INSERT INTO posts (body, created_at, parent_id) VALUES (?1, ?2, ?3)",
    )
    .bind(body, createdAt, parentId)
    .run();
  return res.meta.last_row_id as number;
}

export async function insertPostImage(
  db: D1Database,
  postId: number,
  key: string,
  contentType: string,
  ordinal: number,
  alt: string | null,
): Promise<void> {
  await db
    .prepare(
      `INSERT INTO post_images (post_id, r2_key, content_type, ordinal, alt)
       VALUES (?1, ?2, ?3, ?4, ?5)`,
    )
    .bind(postId, key, contentType, ordinal, alt)
    .run();
}

export async function updatePostBody(
  db: D1Database,
  id: number,
  body: string,
): Promise<void> {
  await db
    .prepare("UPDATE posts SET body = ?1 WHERE id = ?2")
    .bind(body, id)
    .run();
}

export async function deletePost(
  db: D1Database,
  id: number,
): Promise<PostImage[]> {
  const imgs = await imagesForPost(db, id);
  await db.prepare("DELETE FROM posts WHERE id = ?1").bind(id).run();
  return imgs;
}

// The mailing list isn't a real subscription yet — we're collecting
// interested addresses to notify once email sending is wired up. Stored
// with status='pending' so we can drop them into a real confirmation
// flow later without a migration.

export async function findSubscriberByEmail(
  db: D1Database,
  email: string,
): Promise<Subscriber | null> {
  return await db
    .prepare(
      "SELECT id, email, status, token, created_at, confirmed_at FROM subscribers WHERE email = ?1",
    )
    .bind(email)
    .first<Subscriber>();
}

export async function insertInterestedSubscriber(
  db: D1Database,
  email: string,
  createdAt: number,
): Promise<void> {
  await db
    .prepare(
      `INSERT INTO subscribers (email, status, token, created_at)
       VALUES (?1, 'pending', '', ?2)`,
    )
    .bind(email, createdAt)
    .run();
}

export async function countInterestedSubscribers(
  db: D1Database,
): Promise<number> {
  const row = await db
    .prepare(
      "SELECT COUNT(*) AS n FROM subscribers WHERE status = 'pending'",
    )
    .first<{ n: number }>();
  return row?.n ?? 0;
}
