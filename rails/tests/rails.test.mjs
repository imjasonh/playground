import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

test("browser app ships index.html, ES modules, and vendored wasm engine", () => {
  assert.ok(fs.existsSync(path.join(root, "index.html")), "index.html missing");
  assert.ok(fs.existsSync(path.join(root, "styles.css")), "styles.css missing");
  assert.ok(fs.existsSync(path.join(root, "src/main.js")), "src/main.js missing");
  assert.ok(fs.existsSync(path.join(root, "src/renderer.js")), "src/renderer.js missing");
  assert.ok(fs.existsSync(path.join(root, "src/net.js")), "src/net.js missing");
  assert.ok(
    fs.existsSync(path.join(root, "vendor/rails_engine/rails_server.js")),
    "vendored wasm JS glue missing"
  );
  assert.ok(
    fs.existsSync(path.join(root, "vendor/rails_engine/rails_server_bg.wasm")),
    "vendored wasm binary missing"
  );
});

test("vendored wasm engine initializes and simulates a local North America game in Node", async () => {
  const wasmJsPath = path.join(root, "vendor/rails_engine/rails_server.js");
  const wasmBinPath = path.join(root, "vendor/rails_engine/rails_server_bg.wasm");
  const mod = await import(wasmJsPath);
  const bytes = fs.readFileSync(wasmBinPath);
  await mod.default({ module_or_path: bytes });

  const engine = new mod.WasmEngine();
  const map = JSON.parse(engine.get_map_json());
  assert.equal(map.id, "united_states");
  assert.ok(map.mileposts.length > 1500);
  assert.equal(map.cities.length, 51);
  assert.equal(map.cities.filter((c) => c.size === "major").length, 6);

  const state = JSON.parse(
    engine.start_local_game(
      JSON.stringify({
        mode: "fast",
        events_enabled: true,
        players: [
          { name: "Alice", is_bot: true },
          { name: "Bob", is_bot: true },
        ],
        seed: 12345,
      })
    )
  );
  assert.equal(state.phase, "initial_build");
  assert.equal(state.players.length, 2);
  assert.equal(state.players[0].cash, 60);
  assert.equal(state.players[0].hand.length, 5);

  const afterBot = JSON.parse(engine.step_local_ai());
  assert.notEqual(afterBot.current_player, state.current_player);
  assert.ok(afterBot.tracks.length > 0, "bot should build initial track");
});
