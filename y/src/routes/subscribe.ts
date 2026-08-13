import { Hono } from "hono";
import { html } from "hono/html";
import { findSubscriberByEmail, insertInterestedSubscriber } from "../db";
import { isValidEmail } from "../util";
import { layout } from "../views";

export const subscribeRoutes = new Hono<{ Bindings: Env }>();

subscribeRoutes.get("/subscribe", (c) => {
  return c.html(
    layout(
      {
        title: "subscribe",
        siteTitle: c.env.SITE_TITLE,
        siteUrl: c.env.SITE_URL,
      },
      html`<p>Email subscriptions aren't built yet — but the RSS feed is.
          Drop your address and I'll let you know when there's an email
          option too.</p>
        <form method="post" action="/subscribe" class="row">
          <input type="email" name="email" placeholder="you@example.com" required>
          <button type="submit">register interest</button>
        </form>
        <p>Or grab the <a href="/feed.xml">RSS feed</a> right now.</p>`,
    ),
  );
});

subscribeRoutes.post("/subscribe", async (c) => {
  const form = await c.req.formData();
  const email = String(form.get("email") ?? "")
    .trim()
    .toLowerCase();
  if (!isValidEmail(email)) return c.text("invalid email", 400);

  const existing = await findSubscriberByEmail(c.env.DB, email);
  if (!existing) {
    await insertInterestedSubscriber(
      c.env.DB,
      email,
      Math.floor(Date.now() / 1000),
    );
  }

  // Same response either way — no need to leak whether the address is on
  // the list.
  return c.html(
    layout(
      {
        title: "thanks",
        siteTitle: c.env.SITE_TITLE,
        siteUrl: c.env.SITE_URL,
      },
      html`<p class="ok">Got it — you're on the list. I'll reach out
          when email subscriptions are live.</p>
        <p><a href="/">← back</a></p>`,
    ),
  );
});
