# playground

[![CI](https://github.com/imjasonh/playground/actions/workflows/test.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/test.yml)
[![GitHub Pages](https://github.com/imjasonh/playground/actions/workflows/deploy.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/deploy.yml)
[![Cloudflare Workers](https://github.com/imjasonh/playground/actions/workflows/deploy-workers.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/deploy-workers.yml)

A personal playground monorepo for small, self-contained side projects — browser
toys, command-line tools, native Apple apps, and the occasional backend service —
collected in one place for fun and learning. There's no grand plan and no shared
build at the root: each experiment is its own top-level directory that builds,
tests, and ships entirely on its own, whether it's a static browser app deployed
to GitHub Pages, a standalone Go command-line tool, a Rust crate such as a
Cloudflare Worker, or a native macOS / iOS app.

The point is to keep trying things cheap and low-ceremony. Drop in a new
directory, follow a couple of conventions, and open a PR: CI tests whatever
changed, browser apps get a live preview link, and once merged they deploy
themselves to GitHub Pages. The iOS Playground app ships to TestFlight on merge
to `main`; macOS apps are tested on a macOS runner and (with signing secrets)
will ship notarized Sparkle updates. A daily job keeps each project's
dependencies current too, landing an upgrade only when it still builds and
passes tests — so older experiments don't bit-rot.

## Apps

- **[`artillery/`](artillery/)** — a touch-first, turn-based artillery duel with
  shifting wind, destructible terrain, local multiplayer, and an imperfect AI.
- **[`git/`](git/)** — an in-browser, read-only git client: clone a repository
  into local storage and browse its files, branches, and commit history.
- **[`cold-climb/`](cold-climb/)** — a touch-first, two-handle arcade game:
  balance a ball up the wall while avoiding unlit pockets.
- **[`droneski/`](droneski/)** — pilot an FPV camera drone filming a skier on a
  procedurally generated Olympic downhill course.
- **[`hello/`](hello/)** — a minimal static demo.
- **[`kanoodle/`](kanoodle/)** — the Kanoodle puzzle game (5×11 board, 12 pieces).
- **[`webrtc/`](webrtc/)** — serverless, link-based WebRTC app: share a link to
  open a direct peer-to-peer session with video, voice, text, file transfer,
  live location sharing, and live captions (with on-device translation) — all
  with no backend.
- **[`nypd-choppers/`](nypd-choppers/)** — daily flight paths, airborne hours,
  and estimated fuel cost for NYPD Aviation Unit helicopters, from public ADS-B
  data collected by an hourly scrape workflow.
- **[`population-rays/`](population-rays/)** — from any US point, how far a
  filled 5° slice must go in each direction to hit N people, using Meta/CIESIN
  high-resolution population grids.
- **[`web-push-demo/`](web-push-demo/)** — a browser front-end for the
  `web-push` Worker: subscribe/unsubscribe and send notifications end to end.
- **[`life-lab/`](life-lab/)** — draw a Game of Life starting row, watch it
  grow into a 3D-printable tower (time as the Z axis), and export STL or a
  ready-to-slice Bambu 3MF — powered by the `life-stl` Rust crate compiled to
  WebAssembly.

## Tools

Not every top-level directory is a browser app. Go command-line tools, Rust
apps, and Cloudflare Workers live here too. CI builds and tests each changed
Go module, Rust crate, and Cloudflare Worker; because these have no `index.html`,
GitHub Pages deploy and preview workflows skip them:

- **[`gitdb/`](gitdb/)** — query a git repo's history, files, blame, and file
  contents with SQL, via SQLite virtual tables over go-git (Go CLI).
- **[`ocidb/`](ocidb/)** — explore OCI container images on Docker Hub with SQL,
  via SQLite virtual tables over go-containerregistry (Go CLI).
- **[`pasta/`](pasta/)** — multi-language linters and fixers described in CUE
  over tree-sitter ASTs (Go CLI).
- **[`web-push/`](web-push/)** — a Web Push application-server backend
  (RFC 8030/8188/8291/8292) for Cloudflare Workers, in Rust.
- **[`y/`](y/)** — a one-user microblog for Cloudflare Workers, in Rust
  (D1 + R2): 260-char posts, images, RSS. Deployed as Worker `y`.
- **[`inkbot/`](inkbot/)** — e-ink desk-frame backend for Cloudflare Workers:
  hosts one 800×480 B/W PNG, accepts signed uploads, and turns Slack
  `@inkbot` image mentions into dithered frames.
- **[`inkbot-esp32/`](inkbot-esp32/)** — Rust/ESP-IDF firmware for the Waveshare
  ESP32 + 7.5″ panel: poll `inkbot` every minute and refresh when the image
  changes (no OTA/SSH).
- **[`git-server/`](git-server/)** — a git smart-HTTP server for Cloudflare
  Workers, in Rust: repositories in R2, refs in Durable Objects, plus
  file/tree/blame APIs and streaming pack ingest.
- **[`git-fuse/`](git-fuse/)** — a read-only FUSE adapter for `git-server`,
  in Rust: mount a repo and read `refs/<ref>` and `commits/<sha>/<path>` as
  plain files, with reads racing a shared local clone cache against the
  server's read API so first byte never waits on a clone.
- **[`life-stl/`](life-stl/)** — generate a 3D-printable STL of Conway's Game of
  Life with time as the Z axis (Rust CLI). Self-supporting by construction:
  every birth leans on its three B3 parents via small diagonal braces, so even
  gliders print as one piece with no supports to remove.
- **[`vase-stl/`](vase-stl/)** — convert an arbitrary STL into a solid suitable
  for FDM vase / spiral printing by lofting its radial envelope (Rust CLI).
- **[`life-scad/`](life-scad/)** — OpenSCAD Game of Life sculpture (Z = time)
  plus an offline reverse-history searcher for shallow roof targets.
- **[`life-qr/`](life-qr/)** — parametric OpenSCAD Life sculpture whose roof is
  a scannable QR code for any text and height (time runs toward the bed).
- **[`its-not-jaws/`](its-not-jaws/)** — Cursor Agent SDK harness for It's Not
  Jaws: knower picks a movie, guesser uses shared-fact clues; tracks outcomes,
  leaks in published traces, game length, and token cost.

## iOS app

There is a **single** iOS app that builds and tests on a macOS runner and ships
to **TestFlight** on merge to `main` (it isn't deployed to GitHub Pages). Just as
the Pages site hosts many browser apps, this one TestFlight app hosts many
experiments internally:

- **[`ios/`](ios/)** — the **Playground** app: a launcher that hosts many
  self-contained experiments (one folder each under
  `ios/Sources/Experiments/`). Add an experiment by creating that folder,
  self-declaring a `*Experiment.swift`, and appending it to the catalog — no
  new app, no CI changes. Unit + UI tests, continuous delivery to TestFlight.

See [`docs/ios-testflight-design.md`](docs/ios-testflight-design.md) for the iOS
CD/preview design, and [`docs/ios-testflight-setup.md`](docs/ios-testflight-setup.md)
for a click-by-click, beginner-friendly Apple/TestFlight setup guide.

## macOS apps

Unlike iOS (one Playground container), **macOS apps are ordinary top-level
directories** — one app per directory, discovered by an XcodeGen `project.yml`
that declares `platform: macOS`:

- **[`hello-macos/`](hello-macos/)** — minimal SwiftUI "Hello Mac" sample (the
  macOS counterpart of static `hello/`). Discovery, CI, notarized Sparkle CD,
  and in-app **Check for Updates…** against the gh-pages appcast.
- **[`onramp/`](onramp/)** — Onramp offline Mac can’t-get-online triage
  (playbooks + network toolbox; optional on-device chat). Same Sparkle CD path; see
  [`docs/onramp-design.md`](docs/onramp-design.md).

See [`docs/macos-sparkle-design.md`](docs/macos-sparkle-design.md) for the macOS
release design (Developer ID + notarization + Sparkle appcast on GitHub Pages).

See [`AGENTS.md`](AGENTS.md) for repository conventions, CI, and how to add a new app.
