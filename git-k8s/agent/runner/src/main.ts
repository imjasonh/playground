import { runFromEnv } from "./run.js";
import { serveFromEnv } from "./serve.js";

const command = process.argv[2];
if (command === "run") {
  // The SDK can leave handles open after the run, so exit explicitly.
  process.exit(await runFromEnv(process.env));
} else if (command === "serve") {
  const server = await serveFromEnv(process.env);
  // As PID 1, Node gets no default handler for these signals.
  for (const signal of ["SIGTERM", "SIGINT"] as const) {
    process.once(signal, () => {
      server.closeAllConnections();
      server.close(() => process.exit(0));
    });
  }
} else {
  console.error("usage: main.js run | serve");
  process.exit(2);
}
