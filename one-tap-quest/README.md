# One Tap Quest (Unofficial Godot Recreation)

> **Attribution:** This is an unofficial, AI-built Godot 4.7 recreation of **[One Tap Quest](http://shimage.net/one-tap-quest/)** by **[shimage.net](http://shimage.net)** (2014). The game design, one-tap mechanic, enemy roster, patrol patterns, level curve, item effects, map layout, and 9-crystal boss fight all come directly from shimage.net's original Enchant.js game — please play and support the original at [shimage.net/one-tap-quest](http://shimage.net/one-tap-quest/). All code and pixel-art sprites in this directory were written from scratch for this port.

Compiled for **Web** (GitHub Pages) and embedded natively in the **Playground iOS app** (`ios/`) via [SwiftGodotKit](https://github.com/migueldeicaza/SwiftGodotKit).

## How the game works

You get one move per run:

1. **Aim:** Press and drag horizontally at the bottom of the 250×300 dungeon field to pick your starting column.
2. **Launch:** Release to send your hero marching straight north at 1 px/frame (24 fps). Tapping again at any time starts a fresh run.
3. **Level up on the march:** Colliding with an enemy whose `LV <= player.LV` defeats it, grants EXP and score, and nudges the hero back 5 px. Colliding with a stronger enemy ends the run and reveals its level.
4. **Pick up items:**
   - **Sword / Shield:** Instant level up.
   - **Ale (`join`):** Instant level up and recruits two party members, widening the hero hitbox from 12 px to 36 px.
   - **Warp:** Shifts the hero down 40 px and across 80 px to farm another column.
   - **Thunder:** Fires four diagonal lightning orbs at the hero's current level.
5. **Boss stage:** Crossing the top of the field after all thunder orbs leave the screen enters the boss room. The boss has 9 orbiting HP crystals; each hit shatters one crystal and costs 1 hero level, so you need at least **LV 10** to win (+10,000 score bonus).

## Build and test locally

```bash
# Install Godot 4.7.2-stable and Web export templates (Linux x86_64)
GODOT=$(bash .github/scripts/setup-godot.sh)

# Run headless GDScript unit tests
"$GODOT" --headless --path one-tap-quest --script res://tests/test_game_logic.gd

# Export both the iOS .pck (into ios/Sources/Experiments/OneTapQuest/Resources/)
# and the Web build (into one-tap-quest/build/web/)
GODOT="$GODOT" bash one-tap-quest/build.sh all
```

To regenerate the original pixel-art sprites and tileset:

```bash
python3 one-tap-quest/scripts/gen_assets.py
```

## CI and deployment

- **Tests (`test.yml`):** `discover-godot-apps.sh` selects `one-tap-quest` when any file under `one-tap-quest/` changes. The `godot` job runs `tests/test_game_logic.gd` headlessly and verifies both Web and PCK exports.
- **Web (`deploy.yml`, `preview.yml`):** Exports the single-threaded WebGL2/Wasm build (no COOP/COEP headers required) into GitHub Pages and PR previews with `whbiab.js` tracking preserved.
- **iOS (`ios/`):** `ios/Sources/Experiments/OneTapQuest/` embeds `one-tap-quest.pck` inside the single Playground iOS host app using `SwiftGodotKit` (`binary` branch prebuilt XCFrameworks, supporting both iOS devices and Simulator).
