# Rails — Crayon Railroad Empire

Browser-based multiplayer **Empire Builder** (crayon rails) game on the classic North America (US + Southern Canada) map, built for live game nights over Google Meet or local play vs. RailBots.

## Features
- **North America Map**: 542-milepost hex lattice, 6 Major Cities, 34 Medium/Small Cities, Rocky/Cascade/Appalachian mountains, 7 major rivers (`+$2M`), ocean inlets (`+$3M`), 26 commodities, 108 demand cards, and 16 toggleable event cards.
- **Standard & Fast Modes**: Classic rules (`$40M`, 2 initial builds, 9/12 speed) or Fast Mode (`$60M`, 3 initial builds, deal-5-keep-3 cards, 12/16 speed).
- **Live Multiplayer (Google Meet)**: Connects to `../rails-server` (Cloudflare Worker + SQLite Durable Objects) with shareable `?room=CODE` invite links, instant reconnects, and real-time draft track/route previews.
- **Shared Rust/Wasm Engine**: Powered by `vendor/rails_engine/` compiled from `../rails-server`.

## Development
```bash
./build-wasm.sh   # Rebuild vendor/rails_engine from ../rails-server
npm test          # Run Node smoke & Wasm tests
```
