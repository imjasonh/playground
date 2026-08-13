import { Hono } from "hono";
import { publicRoutes } from "./routes/public";
import { adminRoutes } from "./routes/admin";
import { subscribeRoutes } from "./routes/subscribe";

const app = new Hono<{ Bindings: Env }>();

app.route("/", publicRoutes);
app.route("/", subscribeRoutes);
app.route("/admin", adminRoutes);

app.notFound((c) => c.text("not found", 404));
app.onError((err, c) => {
  console.error(err);
  return c.text("internal error", 500);
});

export default app;
