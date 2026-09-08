const args = process.argv.slice(2);
if (args.includes("--hello")) {
  console.log("bun-image-ok");
} else {
  const rawPort = Bun.env.PORT;
  let port = 8000;
  if (rawPort) {
    port = Number(rawPort);
  }
  Bun.serve({
    port,
    fetch() {
      return new Response("Hello world");
    },
  });
  console.log(`http://localhost:${port}/`);
}
