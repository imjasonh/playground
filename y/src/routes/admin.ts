import { Hono } from "hono";
import { getCookie, setCookie, deleteCookie } from "hono/cookie";
import { html, raw } from "hono/html";
import type { Context, Next } from "hono";
import {
  CHALLENGE_COOKIE,
  CHALLENGE_TTL,
  SESSION_COOKIE,
  makeChallengeCookie,
  makeSessionCookie,
  verifyChallengeCookie,
  verifyPassword,
  verifySessionCookie,
} from "../auth";
import {
  countInterestedSubscribers,
  deletePost,
  getPost,
  imagesForPost,
  insertPost,
  insertPostImage,
  updatePostBody,
} from "../db";
import {
  POST_MAX_CHARS,
  formatHuman,
  imageExtFor,
  isAllowedImageType,
} from "../util";
import type {
  AuthenticationResponseJSON,
  RegistrationResponseJSON,
} from "@simplewebauthn/types";
import {
  buildAuthenticationOptions,
  buildRegistrationOptions,
  countCredentials,
  deleteCredential,
  listCredentials,
  verifyAuthentication,
  verifyRegistration,
} from "../passkey";
import { WEBAUTHN_CLIENT_JS } from "../webauthn-client";
import { layout } from "../views";

export const adminRoutes = new Hono<{ Bindings: Env }>();

const SESSION_MAX_AGE = 60 * 60 * 24 * 30;

function setSession(c: Context<{ Bindings: Env }>, value: string) {
  setCookie(c, SESSION_COOKIE, value, {
    path: "/",
    httpOnly: true,
    secure: true,
    sameSite: "Strict",
    maxAge: SESSION_MAX_AGE,
  });
}

function setChallenge(c: Context<{ Bindings: Env }>, value: string) {
  setCookie(c, CHALLENGE_COOKIE, value, {
    path: "/admin",
    httpOnly: true,
    secure: true,
    sameSite: "Strict",
    maxAge: CHALLENGE_TTL,
  });
}

async function requireSession(
  c: Context<{ Bindings: Env }>,
  next: Next,
): Promise<Response | void> {
  const raw = getCookie(c, SESSION_COOKIE);
  const ok = await verifySessionCookie(
    c.env.SESSION_SECRET,
    raw,
    Math.floor(Date.now() / 1000),
  );
  if (!ok) return c.redirect("/admin/login");
  await next();
}

// ---------- Login ----------

adminRoutes.get("/login", async (c) => {
  const err = c.req.query("err");
  const passkeyCount = await countCredentials(c.env.DB);
  const bootstrap = passkeyCount === 0;

  return c.html(
    layout(
      { title: "login", siteTitle: c.env.SITE_TITLE, siteUrl: c.env.SITE_URL },
      html`${!bootstrap
          ? html`<p>
              <button type="button" onclick="pkLogin().catch(e=>document.getElementById('pk-err').textContent=String(e))">
                log in with passkey
              </button>
              <span id="pk-err" class="err"></span>
            </p>`
          : html`<p class="ok">No passkey registered yet. Sign in with the bootstrap password to register one.</p>
            <form method="post" action="/admin/login">
              <p><input type="password" name="password" placeholder="password" autofocus required></p>
              ${err ? html`<p class="err">incorrect password</p>` : ""}
              <p><button type="submit">log in</button></p>
            </form>`}
        <script>${raw(WEBAUTHN_CLIENT_JS)}</script>`,
    ),
  );
});

adminRoutes.post("/login", async (c) => {
  // Bootstrap-only: once a passkey exists, password is dead.
  const passkeyCount = await countCredentials(c.env.DB);
  if (passkeyCount > 0) return c.text("password login disabled", 403);

  const form = await c.req.formData();
  const password = String(form.get("password") ?? "");
  const ok = await verifyPassword(password, c.env.ADMIN_PASSWORD_HASH);
  if (!ok) return c.redirect("/admin/login?err=1");

  const now = Math.floor(Date.now() / 1000);
  setSession(c, await makeSessionCookie(c.env.SESSION_SECRET, now));
  return c.redirect("/admin/passkeys?bootstrap=1");
});

adminRoutes.post("/logout", requireSession, (c) => {
  deleteCookie(c, SESSION_COOKIE, { path: "/" });
  return c.redirect("/");
});

// ---------- Passkey login ----------

adminRoutes.post("/login/passkey/options", async (c) => {
  const opts = await buildAuthenticationOptions(c.env);
  const cookie = await makeChallengeCookie(
    c.env.SESSION_SECRET,
    opts.challenge,
    Math.floor(Date.now() / 1000),
  );
  setChallenge(c, cookie);
  return c.json(opts);
});

adminRoutes.post("/login/passkey/verify", async (c) => {
  const raw = getCookie(c, CHALLENGE_COOKIE);
  const expected = await verifyChallengeCookie(
    c.env.SESSION_SECRET,
    raw,
    Math.floor(Date.now() / 1000),
  );
  deleteCookie(c, CHALLENGE_COOKIE, { path: "/admin" });
  if (!expected) return c.text("challenge expired", 400);

  const response = await c.req.json<AuthenticationResponseJSON>();
  const result = await verifyAuthentication(c.env, expected, response);
  if (!result.ok) return c.text(result.reason, 400);

  const now = Math.floor(Date.now() / 1000);
  setSession(c, await makeSessionCookie(c.env.SESSION_SECRET, now));
  return c.json({ ok: true });
});

// ---------- Passkey management (auth-required) ----------

adminRoutes.get("/passkeys", requireSession, async (c) => {
  const creds = await listCredentials(c.env.DB);
  const bootstrap = c.req.query("bootstrap") === "1";
  return c.html(
    layout(
      {
        title: "passkeys",
        siteTitle: c.env.SITE_TITLE,
        siteUrl: c.env.SITE_URL,
      },
      html`${bootstrap
          ? html`<p class="ok">You're in. Register a passkey now to lock down login — the bootstrap password becomes inactive after the first one is added.</p>`
          : ""}
        <h2>passkeys</h2>
        ${creds.length === 0
          ? html`<p class="empty">none registered.</p>`
          : html`<ul>
              ${creds.map(
                (cred) => html`<li>
                  <strong>${cred.label}</strong>
                  <span class="meta"> — added ${formatHuman(cred.created_at)}</span>
                  <form method="post" action="/admin/passkeys/${cred.id}/delete" style="display:inline" onsubmit="return confirm('delete passkey?')">
                    <button type="submit">delete</button>
                  </form>
                </li>`,
              )}
            </ul>`}
        <h3>add a passkey</h3>
        <form onsubmit="event.preventDefault(); pkRegister(this.label.value).catch(e=>document.getElementById('pk-err').textContent=String(e))" class="row">
          <input type="text" name="label" placeholder="e.g. laptop" required>
          <button type="submit">register</button>
        </form>
        <p id="pk-err" class="err"></p>
        <p><a href="/admin">← back to admin</a></p>
        <script>${raw(WEBAUTHN_CLIENT_JS)}</script>`,
    ),
  );
});

adminRoutes.post("/passkeys/register/options", requireSession, async (c) => {
  const opts = await buildRegistrationOptions(c.env);
  const cookie = await makeChallengeCookie(
    c.env.SESSION_SECRET,
    opts.challenge,
    Math.floor(Date.now() / 1000),
  );
  setChallenge(c, cookie);
  return c.json(opts);
});

adminRoutes.post("/passkeys/register/verify", requireSession, async (c) => {
  const raw = getCookie(c, CHALLENGE_COOKIE);
  const expected = await verifyChallengeCookie(
    c.env.SESSION_SECRET,
    raw,
    Math.floor(Date.now() / 1000),
  );
  deleteCookie(c, CHALLENGE_COOKIE, { path: "/admin" });
  if (!expected) return c.text("challenge expired", 400);

  const body = await c.req.json<{
    label: string;
    response: RegistrationResponseJSON;
  }>();
  const label = String(body.label ?? "passkey").slice(0, 80);
  const result = await verifyRegistration(
    c.env,
    expected,
    body.response,
    label,
  );
  if (!result.ok) return c.text(result.reason, 400);
  return c.json({ ok: true });
});

adminRoutes.post(
  "/passkeys/:id{[0-9]+}/delete",
  requireSession,
  async (c) => {
    const id = Number(c.req.param("id"));
    await deleteCredential(c.env.DB, id);
    return c.redirect("/admin/passkeys");
  },
);

// ---------- Post management ----------

adminRoutes.get("/", requireSession, async (c) => {
  const replyToParam = c.req.query("reply_to");
  const replyToId = replyToParam ? Number(replyToParam) : null;
  const [replyTo, interestCount] = await Promise.all([
    replyToId && Number.isFinite(replyToId)
      ? getPost(c.env.DB, replyToId)
      : Promise.resolve(null),
    countInterestedSubscribers(c.env.DB),
  ]);
  return c.html(
    layout(
      {
        title: "admin",
        siteTitle: c.env.SITE_TITLE,
        siteUrl: c.env.SITE_URL,
      },
      html`${interestCount >= 10
        ? html`<p class="interest-banner">📬 ${interestCount} people have registered interest in email subscriptions — time to wire that up.</p>`
        : ""}
      ${replyTo
        ? html`<p class="reply-ctx">↳ replying to
            <a href="/post/${replyTo.id}">«${replyTo.body.slice(0, 80)}${replyTo.body.length > 80 ? "…" : ""}»</a>
            · <a href="/admin">cancel</a></p>`
        : ""}
      <form method="post" action="/admin/posts" enctype="multipart/form-data">
        ${replyTo ? html`<input type="hidden" name="parent_id" value="${replyTo.id}">` : ""}
        <p><textarea name="body" maxlength="${POST_MAX_CHARS}" autofocus
          placeholder="say something (max ${POST_MAX_CHARS} chars), or just attach an image"
          oninput="var r=${POST_MAX_CHARS}-this.value.length;ycnt.textContent=r;ycnt.className=r<20?'warn':''"
          onkeydown="if((event.metaKey||event.ctrlKey)&&event.key==='Enter'){event.preventDefault();this.form.requestSubmit()}"></textarea></p>
        <p><input type="file" name="image" accept="image/*" multiple></p>
        <p>
          <button type="submit" class="btn">${replyTo ? "reply" : "post"}</button>
          <span class="counter"><output id="ycnt">${POST_MAX_CHARS}</output> left</span>
        </p>
      </form>
      <p class="admin-bottom row">
        <a href="/admin/passkeys">passkeys</a>
        <form method="post" action="/admin/logout" style="display:inline">
          <button type="submit">log out</button>
        </form>
      </p>`,
    ),
  );
});

adminRoutes.post("/posts", requireSession, async (c) => {
  const form = await c.req.formData();
  const body = String(form.get("body") ?? "").trim();
  if (body.length > POST_MAX_CHARS) {
    return c.text(`body exceeds ${POST_MAX_CHARS} chars`, 400);
  }

  // workers-types declares getAll as returning string[], but at runtime
  // multipart entries are File | string. Cast and filter.
  const entries = form.getAll("image") as unknown as (File | string)[];
  const files = entries.filter(
    (v): v is File => typeof v !== "string" && v.size > 0,
  );
  for (const f of files) {
    if (!isAllowedImageType(f.type)) {
      return c.text(`unsupported image type: ${f.type}`, 400);
    }
  }

  if (!body && files.length === 0) {
    return c.text("a post needs text or an image", 400);
  }

  const parentRaw = form.get("parent_id");
  let parentId: number | null = null;
  if (parentRaw != null && String(parentRaw) !== "") {
    const n = Number(parentRaw);
    if (!Number.isFinite(n)) return c.text("bad parent_id", 400);
    const parent = await getPost(c.env.DB, n);
    if (!parent) return c.text("parent post not found", 400);
    parentId = parent.id;
  }

  const now = Math.floor(Date.now() / 1000);
  const postId = await insertPost(c.env.DB, body, now, parentId);

  for (let i = 0; i < files.length; i++) {
    const f = files[i];
    const ext = imageExtFor(f.type);
    const key = `${postId}/${i}.${ext}`;
    await c.env.IMAGES.put(key, f.stream(), {
      httpMetadata: { contentType: f.type },
    });
    await insertPostImage(c.env.DB, postId, key, f.type, i, null);
  }

  // Keep the chain going: land on a reply form for the post we just
  // created. Click "cancel" in the reply-ctx bar to break the chain.
  return c.redirect(`/admin?reply_to=${postId}`);
});

adminRoutes.post("/posts/:id{[0-9]+}/delete", requireSession, async (c) => {
  const id = Number(c.req.param("id"));
  const imgs = await deletePost(c.env.DB, id);
  await Promise.all(imgs.map((i) => c.env.IMAGES.delete(i.r2_key)));
  return c.redirect("/admin");
});

adminRoutes.get("/posts/:id{[0-9]+}/edit", requireSession, async (c) => {
  const id = Number(c.req.param("id"));
  const post = await getPost(c.env.DB, id);
  if (!post) return c.notFound();
  return c.html(
    layout(
      { title: "edit", siteTitle: c.env.SITE_TITLE, siteUrl: c.env.SITE_URL },
      html`<h2>edit post #${id}</h2>
        <form method="post" action="/admin/posts/${id}/edit">
          <p><textarea name="body" maxlength="${POST_MAX_CHARS}"
            oninput="var r=${POST_MAX_CHARS}-this.value.length;ycnt.textContent=r;ycnt.className=r<20?'warn':''"
            onkeydown="if((event.metaKey||event.ctrlKey)&&event.key==='Enter'){event.preventDefault();this.form.requestSubmit()}">${post.body}</textarea></p>
          <p>
            <button type="submit">save</button>
            <a href="/post/${id}">cancel</a>
            <span class="counter"><output id="ycnt" class="${POST_MAX_CHARS - post.body.length < 20 ? "warn" : ""}">${POST_MAX_CHARS - post.body.length}</output> left</span>
          </p>
        </form>`,
    ),
  );
});

adminRoutes.post("/posts/:id{[0-9]+}/edit", requireSession, async (c) => {
  const id = Number(c.req.param("id"));
  const form = await c.req.formData();
  const body = String(form.get("body") ?? "").trim();
  if (body.length > POST_MAX_CHARS) {
    return c.text(`body exceeds ${POST_MAX_CHARS} chars`, 400);
  }
  if (!body) {
    const imgs = await imagesForPost(c.env.DB, id);
    if (imgs.length === 0) {
      return c.text("a post needs text or an image", 400);
    }
  }
  await updatePostBody(c.env.DB, id, body);
  return c.redirect(`/post/${id}`);
});
