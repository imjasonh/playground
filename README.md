# playground

[![CI](https://github.com/imjasonh/playground/actions/workflows/test.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/test.yml)
[![GitHub Pages](https://github.com/imjasonh/playground/actions/workflows/deploy.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/deploy.yml)
[![Cloudflare Workers](https://github.com/imjasonh/playground/actions/workflows/deploy-workers.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/deploy-workers.yml)

This is a pile of small projects I actually wanted to build. Each top-level
directory is one experiment. It builds, tests, and ships on its own: a static
page on GitHub Pages, a Go CLI, a Rust Cloudflare Worker, an iOS experiment
inside the one TestFlight app, or a macOS app. There is no shared build at the
root. There is no grand plan.

Adding a new one should stay cheap. Make a directory, follow a couple of
conventions, open a PR. CI tests whatever you touched. Browser apps get a live
preview. Merge to `main` and they ship: GitHub Pages for the web apps,
TestFlight for iOS, notarized Sparkle updates for macOS if the signing secrets
are present. A daily job bumps each project's dependencies, and only lands the
bump when the tests still pass, so old experiments don't rot.

## Apps

- **[`artillery/`](artillery/)** — a touch-first, turn-based artillery duel with
  shifting wind, destructible terrain, local multiplayer, and an imperfect AI.
- **[`git/`](git/)** — an in-browser, read-only git client: clone a repository
  into local storage and browse its files, branches, and commit history.
- **[`cold-climb/`](cold-climb/)** — a touch-first, two-handle arcade game:
  balance a ball up the wall while avoiding unlit pockets.
- **[`droneski/`](droneski/)** — pilot an FPV camera drone filming a skier on a
  procedurally generated Olympic downhill course.
- **[`esp-flash/`](esp-flash/)** — flash `inkbot-esp32` / `maze-esp32` (or a
  local `.bin`) to a USB ESP32 from Chrome or Edge.
- **[`hello/`](hello/)** — a minimal static demo.
- **[`sundial/`](sundial/)** — a clock whose long shadow follows the sun, like
  a sundial. At night there is no shadow.
- **[`kanoodle/`](kanoodle/)** — the Kanoodle puzzle game (5×11 board, 12 pieces).
- **[`kubescheduler-the-game/`](kubescheduler-the-game/)** — play the Kubernetes
  scheduler and cluster operator: bin-pack pods onto nodes, handle spot
  reclaims and rolling upgrades, and keep utilization high without overspending.
- **[`webrtc/`](webrtc/)** — serverless, link-based WebRTC app: share a link to
  open a direct peer-to-peer session with video, voice, text, file transfer,
  live location sharing, and live captions with on-device translation. No
  backend.
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
  ready-to-slice Bambu 3MF. Powered by the `life-stl` Rust crate compiled to
  WebAssembly.

## Tools

Not every top-level directory is a browser app. Go CLIs, Rust crates, and
Cloudflare Workers live here too. CI still builds and tests them when they
change. They have no `index.html`, so GitHub Pages deploy and preview skip
them:

- **[`gitdb/`](gitdb/)** — query a git repo's history, files, blame, and file
  contents with SQL, via SQLite virtual tables over go-git (Go CLI).
- **[`ocidb/`](ocidb/)** — explore OCI container images on Docker Hub with SQL,
  via SQLite virtual tables over go-containerregistry (Go CLI).
- **[`pasta/`](pasta/)** — multi-language linters and fixers described in CUE
  over tree-sitter ASTs (Go CLI).
- **[`sshapp/`](sshapp/)** — Wish SSH apps on GKE Autopilot behind one SSH mux
  (`hello`, `chess`; Terraform + `ko_build`).
- **[`web-push/`](web-push/)** — a Web Push application-server backend
  (RFC 8030/8188/8291/8292) for Cloudflare Workers, in Rust.
- **[`y/`](y/)** — a one-user microblog for Cloudflare Workers, in Rust
  (D1 + R2): 260-char posts, images, RSS. Deployed as Worker `y`.
- **[`inkbot/`](inkbot/)** — e-ink desk-frame backend for Cloudflare Workers:
  hosts one 800×480 B/W PNG, accepts signed uploads, and turns Slack
  `@inkbot` image mentions into dithered frames.
- **[`inkbot-esp32/`](inkbot-esp32/)** — Rust/ESP-IDF firmware for the Waveshare
  ESP32 + 7.5″ panel: poll `inkbot` every minute, signed OTA from GHCR
  after a USB NVS provision, or flash `APP=maze` for an offline maze that
  partial-refreshes a correct solve.
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
- **[`mapvelopes/`](mapvelopes/)** — printable US envelope PDFs with the
  driving route from sender to recipient as the background (Rust Cloudflare
  Worker, plus a native CLI for spot-checking).
- **[`life-scad/`](life-scad/)** — OpenSCAD Game of Life sculpture (Z = time)
  plus an offline reverse-history searcher for shallow roof targets.
- **[`life-qr/`](life-qr/)** — parametric OpenSCAD Life sculpture whose roof is
  a scannable QR code for any text and height (time runs toward the bed).
- **[`its-not-jaws/`](its-not-jaws/)** — Cursor Agent SDK harness for It's Not
  Jaws: knower picks a movie, guesser uses shared-fact clues; tracks outcomes,
  leaks in published traces, game length, and token cost.

## iOS app

There is one iOS app. It builds on a macOS runner and ships to **TestFlight** on
merge to `main`. It is not published to GitHub Pages. Experiments live as folders
inside the app, not as extra iOS projects.

- **[`ios/`](ios/)** — the **Playground** app: a launcher that hosts many
  experiments (one folder each under `ios/Sources/Experiments/`). Add an
  experiment by creating that folder, self-declaring a `*Experiment.swift`, and
  appending it to the catalog. No new app, no CI changes. Unit + UI tests,
  continuous delivery to TestFlight.

See [`docs/ios-testflight-design.md`](docs/ios-testflight-design.md) for the iOS
CD/preview design, and [`docs/ios-testflight-setup.md`](docs/ios-testflight-setup.md)
for a click-by-click Apple/TestFlight setup guide.

## macOS apps

macOS apps are ordinary top-level directories. One app per directory. CI finds
them from an XcodeGen `project.yml` that declares `platform: macOS`:

- **[`hello-macos/`](hello-macos/)** — minimal SwiftUI "Hello Mac" sample (the
  macOS counterpart of static `hello/`). Discovery, CI, notarized Sparkle CD,
  and in-app **Check for Updates…** against the gh-pages appcast.
- **[`onramp/`](onramp/)** — Onramp offline Mac can’t-get-online triage
  (playbooks + network toolbox; optional on-device chat). Same Sparkle CD path; see
  [`docs/onramp-design.md`](docs/onramp-design.md).

See [`docs/macos-sparkle-design.md`](docs/macos-sparkle-design.md) for the macOS
release design (Developer ID + notarization + Sparkle appcast on GitHub Pages).

Human-authored project posts (`blog-post.md` next to an experiment) publish to
[`/posts/`](https://imjasonh.github.io/playground/posts/) (with an
[RSS feed](https://imjasonh.github.io/playground/posts/feed.xml)). The home
page header links to that catalog.

See [`AGENTS.md`](AGENTS.md) for repository conventions, CI, and how to add a new app.
