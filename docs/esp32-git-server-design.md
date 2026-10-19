# Design: a git server on an ESP32 with an SD card

> **Status:** design only. No code exists yet. This document proposes a new
> top-level Rust firmware crate, `git-esp32/`, built on ESP-IDF like
> [`inkbot-esp32/`](../inkbot-esp32/). Numbers marked *estimated* come from
> published benchmarks and host measurements. Milestone 0 replaces them with
> measurements on the device.

## Summary

An ESP32 can run a git smart-HTTP server that stock `git` clients clone from
and push to, with repositories stored on a microSD card. The recommended build
is:

- An ESP32-S3 module with 8 MiB of octal PSRAM and a microSD slot wired for
  4-bit SD mode.
- Rust on ESP-IDF through `esp-idf-svc`, the same stack as `inkbot-esp32/` and
  `esp32-ble/`.
- Plain HTTP on a trusted network, with per-user tokens.
- A log-structured object store on a raw SD partition instead of FAT.
- The architecture of [`git-server/`](../git-server/docs/design.md): immutable
  packs, a small versioned ref state, a streaming pack scanner, and fetch
  responses that copy stored compressed bytes instead of recompressing them.

Three limits shape the rest of the design:

1. **Accepting a push is CPU work.** Pack entries don't carry object IDs, so
   the server inflates every entry and rebuilds every delta to compute the
   SHA-1 of each full object. In the measured packs, that means hashing 8 to
   20 times the pack size. Large pushes of source history index at an
   estimated 0.5 to 1.5 MiB/s of pack, which is slower than Wi-Fi.
2. **Wi-Fi airtime limits small operations.** An up-to-date `git fetch` or a
   one-commit push costs about 11 to 16 radio frames between the access point
   and the ESP32. That caps the device at an estimated 100 to 300 small
   operations per second.
3. **TLS is expensive.** Espressif's HTTPS server documentation puts the first
   session setup at about two seconds, and every `git` command opens a new
   connection. HTTPS would hold the device near one operation per second, so
   the default transport is HTTP.

Estimated ceilings for an ESP32-S3 with a strong signal on an uncongested
2.4 GHz channel:

| Operation | Estimated ceiling | What limits it |
|---|---|---|
| Up-to-date `git fetch` | 100-300 per second across all clients | Radio frames per operation. The response comes from RAM. |
| Push of one small commit | 100-250 per second across all clients | Radio frames per operation. Grouped commits keep the SD card off the critical path. |
| Fetch of one new push | 100-250 per second. Repeats replay a cached response. | Object selection and radio frames |
| Clone or large fetch | 2.5-10 MB/s across all clients | Wi-Fi throughput |
| Large push of already-compressed files | 2.5-10 MB/s | Wi-Fi throughput |
| Large push of source history | 0.5-1.5 MiB/s of pack | Single-core inflate and PSRAM bandwidth for delta rebuilds |

For large packs, the design does the following:

- Streams each pack straight to its own segments on the card, with no size
  cap and no whole-pack buffer.
- Indexes the pack while it arrives. For a typical incremental push, almost
  every delta is rebuilt before the last byte lands.
- Sends progress and keepalive packets so the connection stays open during
  long indexing.

For operations per second, the design does the following:

- Answers ref advertisements and `ls-refs` from RAM.
- Finishes every fetch in one round trip, and replays a cached response for
  identical fetches.
- Groups pushes into shared SD writes, and lets pushes to different refs land
  without conflicts.
- Keeps freshly pushed objects in RAM for the fetches that usually follow.
- Repacks in small background steps, so the number of packs, and the work
  every request does, stays low.
- Serves every connection from one polling loop, with Wi-Fi power save off.

Sizes in this document use KiB, MiB, and GiB. Rates use MB/s and Mbit/s, as
the cited benchmarks do.

## Goals and non-goals

Goals:

- Stock `git` 2.26 or later clones, fetches, and pushes over smart HTTP with
  nothing configured but the URL.
- Pushes have no size limit other than free SD space, including single packs
  of several GiB.
- The device handles as many operations per second as the radio allows, with
  many concurrent clients.
- An acknowledged push survives a power cut at any instant, and refs never
  point at missing objects.
- Memory use is bounded. No operation needs RAM in proportion to the
  repository or the pack, except per-object scan metadata during a push,
  which has a documented limit.
- One card holds many repositories.

Non-goals for the first version:

- SSH and `git://` transports.
- SHA-256 repositories.
- Server-side hooks, a web UI, Git LFS, and signed pushes.
- Partial clone and date-based shallow fetch. Depth-based shallow fetch is a
  later milestone.
- Finding new deltas or recompressing objects. The device has no equivalent of
  `git gc --aggressive`.

## Hardware

### Chip

Only three Espressif chip families have an SD host controller. The others
drive cards in SPI mode, which measured two to five times slower than 4-bit SD
mode in one ESP32-S3 benchmark.

| Chip | CPU | RAM | SD | Radio | Fit |
|---|---|---|---|---|---|
| ESP32 | 2 × Xtensa LX6, 240 MHz | 520 KiB SRAM, up to 4 MiB of quad PSRAM mapped | 4-bit host, 40 MHz | 802.11n, 2.4 GHz | Works, but slower. ESP-IDF's floors for its SHA engine are 5 to 15 times lower than the S3's, and the engine serves one hash at a time. |
| ESP32-S3 | 2 × Xtensa LX7, 240 MHz | 512 KiB SRAM, 8 MiB of octal PSRAM on N16R8 modules | 4-bit host, 40 MHz | 802.11n, 2.4 GHz | Recommended |
| ESP32-P4 | 2 × RISC-V, up to 400 MHz | 768 KiB SRAM, up to 32 MiB PSRAM | SD 3.0 host | None. Wi-Fi needs a companion chip, such as an ESP32-C6 over SDIO. It has an Ethernet MAC. | Upgrade path if indexing speed matters more than a single-chip build |
| ESP32-C3, C5, C6 | 1 × RISC-V | At most 512 KiB SRAM | SPI mode only | 2.4 GHz. The C5 adds 5 GHz Wi-Fi 6. | Not recommended: one core and slow SD access |

The ESP32-S3 fits best for four reasons:

- It has an SD host controller and octal PSRAM, which moves 16 bits per clock
  against 4 for the classic ESP32's quad PSRAM.
- Its SHA engine is fast. ESP-IDF's performance tests require it to hash
  32 KiB with SHA-1 in at most 1 ms, which is at least 32 MB/s, and to run
  SHA-256 at 90 MB/s or more. The classic ESP32's floors are 5 to 15 times
  lower.
- Its SHA engine can switch between hash contexts. A push always hashes two
  streams at once: the whole pack, for its trailing checksum, and the current
  object. On the classic ESP32, one context holds the SHA-1 engine and the
  other falls back to software.
- It uses the same Xtensa toolchain (`espup`) as the ESP32 crates already in
  this repository.

### Board and card

- **Module.** An ESP32-S3 with 16 MiB of flash and 8 MiB of octal PSRAM, such
  as the ESP32-S3-WROOM-1-N16R8. The flash holds two OTA slots.
- **SD wiring.** CLK, CMD, and D0 through D3, with 10 kΩ pull-ups on CMD and
  the data lines, running at 40 MHz (`SDMMC_FREQ_HIGHSPEED`). One-bit mode
  halves throughput, and SPI mode is slower still. For more information, see
  [SPI-mode SD wiring](#spi-mode-sd-wiring).
- **Card.** An industrial or high-endurance card with power-loss protection,
  for example one that runs its flash in pSLC mode. When power fails during a
  write, a consumer TLC card can corrupt pages it wrote earlier, including
  data the server already acknowledged. Firmware can detect that damage but
  can't prevent it. An A1 rating helps random reads. A2 cards need host
  support for command queuing and a card cache, which ESP-IDF doesn't enable,
  so they perform like A1 cards.
- **Power.** A 5 V supply that holds up during Wi-Fi bursts and SD writes.
  Optionally, a supercapacitor and a GPIO that senses input power let the
  firmware stop issuing writes before a brownout.

### SPI-mode SD wiring

Some small boards and add-ons wire the card for SPI mode, which uses one data
line in each direction. One example is a Seeed XIAO ESP32S3 with Adafruit's
microSD BFF add-on (product 5683). The XIAO meets the chip requirements: an
ESP32-S3R8 with 8 MiB of octal PSRAM, 8 MiB of flash, which holds two OTA
slots, and an external antenna connector. The BFF's schematic connects only
the card's CS, MOSI, MISO, and SCK pins, leaves DAT1 and DAT2 unconnected, and
has no pull-up resistors. The XIAO ESP32S3 Sense's built-in slot is also wired
for SPI mode, with chip select on GPIO21.

The firmware supports SPI mode through ESP-IDF's SDSPI host behind the same
`BlockDevice` trait, with these costs:

- One ESP32-S3 benchmark measured 1.0 MB/s raw writes and 1.7 MB/s raw reads
  in SPI mode at 20 MHz, against 2.3 and 8.4 MB/s in 4-bit mode on the same
  board. Clones, fetches of objects that aren't cached in RAM, and large pushes
  of binary files run at card speed instead of Wi-Fi speed.
- Up-to-date fetches and small pushes barely change. RAM answers the first,
  and grouped commits spread card writes across many of the second.
- Large pushes of source history already index at about card speed. The
  ingest path stops reading the socket when the scanner falls behind,
  instead of reading the pack back from a card that is slower than Wi-Fi.
- ESP-IDF requires pull-ups on CMD and all four data lines, even in SPI mode.
  The firmware enables the ESP32-S3's internal pull-ups on the connected
  lines, but the BFF's DAT1 and DAT2 can't be pulled up without rework.
  Adafruit sells the BFF for any card that supports SPI mode, but a server
  that runs unattended is safer with pull-ups on every line.
- The BFF's chip select defaults to the XIAO's TX pin, GPIO43, which carries
  UART0 output. Route the ESP-IDF console to USB Serial/JTAG
  (`CONFIG_ESP_CONSOLE_USB_SERIAL_JTAG`), or move chip select to A0 or A1 with
  the BFF's solder jumpers.

For full speed on a XIAO, wire a breakout that brings out all six SD lines with
pull-ups, such as Adafruit's microSD SPI or SDIO breakout (product 4682), to
six free pins. The ESP32-S3 routes its SD host through the GPIO matrix, so any
free pins work. Keep the wires short at 40 MHz.

## What the hardware can do

| Resource | Figure | Source |
|---|---|---|
| Wi-Fi TCP receive | 20 Mbit/s over the air in Espressif's lab, 73 Mbit/s in a shielded box | [ESP-IDF Wi-Fi performance guide][wifi-perf] |
| Wi-Fi TCP send | 20 Mbit/s over the air, 83 Mbit/s in a shielded box | [ESP-IDF Wi-Fi performance guide][wifi-perf] |
| Free internal RAM with Wi-Fi running | About 134-274 KB, depending on Wi-Fi buffer settings | [ESP-IDF Wi-Fi performance guide][wifi-perf] |
| SD raw writes, 4-bit at 40 MHz | About 10 MB/s with 20 KiB multi-block writes in one report, 2.3 MB/s in another | [esp-idf#11628][sd-issue], [esp32-sdcard-msc][sd-msc] |
| SD raw reads, 4-bit at 40 MHz | 8.4 MB/s. The bus limit is 20 MB/s. | [esp32-sdcard-msc][sd-msc] |
| SD raw writes and reads, SPI mode at 20 MHz | 1.0 MB/s writes, 1.7 MB/s reads | [esp32-sdcard-msc][sd-msc] |
| SD writes from a PSRAM or unaligned buffer | Single 512-byte block writes on ESP-IDF 5.2 | [`sdmmc_cmd.c` in ESP-IDF 5.2.2][sdmmc-522] |
| FAT through ESP-IDF's VFS, classic ESP32 | 0.35-3.7 MB/s writes, depending on block size and alignment | [esp32-sd-card-benchmarks][drorgl] |
| SHA-1 in hardware | At least 32 MB/s | [ESP-IDF performance targets for the ESP32-S3][perf-s3] |
| `memcpy` within internal SRAM | 366 MB/s | [esp32-s3-memorycopy][memcopy] |
| `memcpy` between PSRAM and internal SRAM | 32-58 MB/s | [esp32-s3-memorycopy][memcopy] |
| `memcpy` within PSRAM | 21 MB/s | [esp32-s3-memorycopy][memcopy] |
| zlib inflate | Estimated 3-5 MB/s of output per core | [Indexing cost](#indexing-cost) |
| TLS session setup on the server | About 2 s | [ESP-IDF HTTPS server documentation][https-server] |
| lwIP limits | At most 253 sockets. TIME_WAIT lasts 120 s by default. | [ESP-IDF lwIP Kconfig][lwip-kconfig] |

### Indexing cost

To accept a push, the server must know every object's ID, and a pack doesn't
record them. The server computes each ID as the SHA-1 of the object's full
content, so it inflates every entry and applies every delta. The following
measurements come from running `git-server`'s scanner and resolver over three
real packs. The [appendix](#appendix-how-the-indexing-numbers-were-measured)
describes the method.

| Pack | Pack size | Objects | Inflated by the scan | Content hashed | Largest object | Deepest delta chain |
|---|---|---|---|---|---|---|
| ripgrep, full history | 5.7 MiB | 14,062 | 13.4 MiB | 118 MiB | 0.57 MiB | 20 |
| This repository, last 400 commits | 30 MiB | 20,006 | 74 MiB | 248 MiB | 7.9 MiB | 27 |
| This repository, full history | 138 MiB | 45,042 | 404 MiB | 1,412 MiB | 41.7 MiB | 35 |

What the numbers mean for the device:

- The server hashes 8 to 20 times the pack size, because each delta expands to
  a full object before hashing.
- Most objects are small. Between 84 and 87 percent are 16 KiB or less, and 96
  to 97 percent are 64 KiB or less. Small objects can be rebuilt entirely in
  internal SRAM.
- Inflate costs about 38 x86-64 instructions per inflated byte on ripgrep's
  small objects, counted with callgrind. Assuming an LX7 needs roughly 1.3
  times as many instructions for the same work and completes 0.7 to 0.9 of
  them per cycle, inflate runs at 3 to 5 MB/s per core at 240 MHz.
- The scan is serial. A zlib stream has no length prefix, so the only way to
  find where the next entry starts is to inflate the current one. A large push
  therefore inflates on one core, while the other core rebuilds deltas and
  feeds the SHA engine.
- In `git-server`'s scanner, 72 percent of scan instructions are overhead that
  a port removes: a newly zeroed 43 KB inflater for every object (19 percent)
  and `Vec::drain` on the carry buffer (53 percent).

Estimated time to index each pack on an ESP32-S3, next to the time to receive
it:

| Pack | Index on the device | Receive over Wi-Fi at 2.5-10 MB/s | Indexing rate |
|---|---|---|---|
| ripgrep | 5-10 s | 0.6-2.4 s | 0.6-1.1 MiB/s of pack |
| This repository, last 400 commits | 20-30 s | 3-13 s | 1-1.5 MiB/s of pack |
| This repository, full history | 3-5 minutes | 15-58 s | 0.5-0.8 MiB/s of pack |

For source history, indexing sets the push speed, not Wi-Fi. Packs of
already-compressed files, such as images or archives, behave differently. Git
rarely deltifies them, and zlib stores them in uncompressed blocks, so the
scan runs close to SHA-1 speed and the push runs at Wi-Fi speed.

### Request-rate cost

At 802.11n MCS7 on an idle 20 MHz channel, a small frame and its
acknowledgment take an estimated 200 to 250 µs of airtime, including
contention. An up-to-date `git fetch` with protocol v2 opens a TCP connection,
makes two HTTP requests on it, and closes it. That is about 11 or 12 frames
between the access point and the ESP32, or about 2.7 ms of airtime, which caps
the device near 370 such fetches per second when clients are wired to the
access point. Clients on the same radio need twice the airtime. A one-commit
push needs about 14 to 16 frames. The CPU cost of a small operation is
estimated at around a millisecond, so the radio is likely to run out first.
Real channels carry other traffic and retransmissions, which is why the
planning range is 100 to 300 operations per second.

For comparison, `git-server` measured about 6.7 pushes per second per
repository on Cloudflare Workers, limited by its test client, with pushes
taking about 2 s, mostly in R2 reads
([load test](../git-server/docs/loadtest-scaling.md)). On a LAN, a small push
to the device takes tens of milliseconds.

## Architecture

```
                     Wi-Fi and lwIP (core 0)
                              │
             ┌────────────────▼─────────────────┐
             │ net loop (core 0)                │
             │ HTTP/1.1, pkt-lines, side-band,  │
             │ answers from RAM caches          │
             └───────┬──────────────────┬───────┘
                   jobs          pack bytes in and out
     ┌───────────────▼──┐  ┌────────────▼─────┐  ┌──────────────────┐
     │ index worker     │  │ fetch planner    │  │ maintenance      │
     │ (core 1)         │  │ (core 1)         │  │ (core 1, lowest) │
     └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘
              └─────────────┬───────┴─────────────────────┘
                    ┌───────▼─────────┐       ┌──────────────────┐
                    │ store: log,     │◀─────▶│ SD I/O task      │── SDMMC, 4-bit, DMA
                    │ indexes, caches │       │ (one queue)      │
                    └─────────────────┘       └──────────────────┘
```

- The net loop is one task that polls every socket. It parses HTTP/1.1 and
  pkt-lines, answers ref advertisements from RAM, and moves pack bytes between
  sockets and the store. Connections don't get their own tasks, so an idle
  connection costs a socket and a small state struct instead of a 16 KiB
  stack.
- The index worker scans pushed packs, rebuilds deltas, and builds index runs.
- The fetch planner selects the objects that a fetch needs and produces a plan
  that the net loop streams. It runs at a higher priority than the index
  worker, so a long import doesn't stall fetches.
- The store owns the SD layout, grouped commits, recovery, indexes, and
  caches.
- The SD I/O task owns the card. It has one queue, DMA buffers in internal
  SRAM, and issues multi-block transfers.
- Maintenance repacks, caps delta chains, collects garbage, and writes
  checkpoints, at the lowest priority.

The core library does no I/O of its own. Protocol handlers are state machines
that take bytes in and hand bytes out, and storage goes through a
`BlockDevice` trait. The same code runs in host tests, in a host tool that
serves card images, and on the device.

### Memory budget

Internal SRAM is the scarcest resource. The SD controller's DMA reaches only
internal RAM, inflate is fastest with its window there, and Wi-Fi and lwIP
take a large share. The starting budget:

| Internal SRAM use | Size |
|---|---|
| SD DMA buffers | 2 × 16 KiB |
| Scanner inflater: 32 KiB window plus tables | About 44 KiB |
| Rebuild arena for small objects: base plus output buffer | 64 KiB |
| Task stacks | About 40 KiB |
| Total | About 180 KiB |

Espressif's tables leave about 134 to 274 KB free with Wi-Fi running,
depending on buffer settings, so this budget fits only with care. Milestone 2
measures it on the board.

PSRAM holds everything sized by the repository or by traffic. The budget is
elastic: while a large push runs, the caches shrink to make room for scan
metadata.

| PSRAM use | Normal | During a large push |
|---|---|---|
| Object cache: inflated commits, trees, recent blobs, and delta bases | 3 MiB | 1 MiB |
| Block cache: compressed pages and index pages | 1.5 MiB | 0.5 MiB |
| Index filters and fanouts, recent-object table, commit-graph pages | 1.5 MiB | 1.5 MiB |
| Small-push buffers and response caches | 1 MiB | 0.5 MiB |
| Scan metadata | None | 4 MiB |
| Allocator slack | 1 MiB | 0.5 MiB |

Scan metadata takes about 20 bytes per entry, because object IDs go to the
index builder as soon as they're known. At that size, 4 MiB covers about
200,000 objects in one push. Larger pushes need a later spill-to-SD mode, or
need to be split into several pushes, as `git-server` documents for its own
push limit.

## Storage

### Why not FAT

FAT is the obvious choice for the card, and the wrong one for objects and
refs:

- Every pack written as a file costs directory and allocation-table updates.
  Those are small random writes, the slowest thing an SD card does.
- FAT has no journal and no atomic rename, so "the pack is complete and the
  ref points at it" can't be made atomic across a power cut.
- ESP-IDF builds FatFs without exFAT, so a file stops at 4 GiB.
- Writes through ESP-IDF's VFS measured 0.35 to 3.7 MB/s on a classic ESP32,
  against about 10 MB/s for raw multi-block writes on an ESP32-S3.

Alternatives considered:

- littlefs is safe across power cuts, but it slows down on large media when it
  compacts metadata, and its default file size limit is 2 GiB.
- FAT with large preallocated contiguous files, created with FatFs `f_expand`
  (which ESP-IDF enables) and then addressed by sector, keeps the card
  readable on a computer while giving the store regions that write at raw
  speed. It's the fallback if a raw partition proves awkward.

### Card layout

When provisioning allows it, the firmware formats a blank card with an MBR and
two partitions:

1. A small FAT32 partition, for example 256 MiB, for a `README.txt` file,
   logs, crash dumps, and optional bundle exports. It's optional in the first
   version.
2. A raw partition of type `0xDA`, for non-filesystem data, that holds the
   store.

### Log-structured store

The store divides its partition into 4 MiB segments, or segments the size of
the card's allocation unit from its SD status register if that is larger.
Repositories are namespaces inside one store. Each has its own refs, pack
list, index runs, and commit graph, and all of them share one hot log, so the
card sees one sequential stream of writes.

- **Hot log segments** hold 4 KiB-aligned log blocks. Each block has a header
  with a magic number, a sequence number, and a length, followed by records
  and a CRC32C. Records carry small pushes' packs and their index fragments,
  ref updates, descriptors for large packs, repack swaps, and segment frees.
- **Pack segments** hold the raw bytes of large packs. Each large push writes
  its own extents, so concurrent large pushes don't interleave.
- **Index segments** hold sorted index runs.
- **Checkpoint segments** hold a full snapshot: the refs, pack manifest, and
  index manifest of every repository, plus the state of every segment.

Two superblocks in different segments, written alternately, name the newest
checkpoint.

The store follows three write rules:

- Every transfer uses an internal, DMA-capable, 4-byte-aligned buffer of at
  least 16 KiB and goes to the card as one multi-block command. On ESP-IDF
  5.2, a buffer in PSRAM silently turns into single 512-byte block writes,
  which matches the drop at 32 KiB and above in the FAT benchmark.
- Writes within a segment are sequential, and segments are allocated
  round-robin, the access pattern that SD card controllers handle best.
- When the store frees a segment, it can send the card a discard for it with
  `sdmmc_erase_sectors`.

### Grouped commits

A push becomes durable in this order:

1. Its pack bytes reach the card. A small pack travels in the same log block
   as its ref update. A large pack's segments finish writing first.
2. The store writes a log block that contains the push's ref-update record,
   and the card reports the write as complete.
3. The in-RAM ref table changes, cached advertisements are dropped, and
   report-status tells the client `ok`.

Pushes share log blocks. While one block write is in flight, new commit
records queue up, and the next write takes all of them. Nothing waits on a
timer, so batching only happens under load. A 4 KiB write takes 1 to 3 ms on
a typical card, so storage can commit several hundred groups per second, far
more than the radio can deliver.

Ref updates follow the merge-apply rule that `git-server`'s load test forced:
a ref update succeeds if that ref still has the old value the client saw.
Pushes to different refs never conflict. Only a race on the same ref fails,
with `fetch first`, and only for that ref. With the `atomic` capability, all
of a push's ref updates land or none do.

### Recovery

At boot, the store reads both superblocks, loads the newest valid checkpoint,
and replays log blocks whose sequence numbers continue without a gap and whose
CRCs match. It stops at the first block that fails. Nothing after that point
was acknowledged to a client, so dropping it is safe. New writes start in a
fresh segment, never in the partly written one, because some cards corrupt
nearby pages when a page is programmed again after a power cut.

A checkpoint every few seconds, or every few hundred log blocks, keeps replay
under a second.

### Reclaiming space

Packs and segments never change after a commit record references them. A
repack writes new segments and then commits a swap record that replaces the
consumed packs in the manifest. The store frees the old segments only after
every in-flight request that took its snapshot before the swap finishes,
which reference counts track. `git-server`'s load test found that deleting at
swap time failed about 5 percent of in-flight pushes, so this rule isn't
optional.

## Object database

### One pack per push

The store keeps each push's pack byte for byte, including thin packs whose
deltas refer to objects in earlier packs. There are no loose objects.

### Indexes

Each pack gets an index run sorted by object ID. An entry holds the object ID,
the offset in the pack, the compressed length, the final type and size, and
the position of its delta base, which is about 40 bytes on the card. RAM holds
a 256-entry fanout and a Bloom filter for each run, at about 10 bits per
object for roughly a 1 percent false-positive rate, so lookups of absent
objects, such as `have` lines and thin-base checks, usually skip the card. A
lookup of an object that exists costs one page read, often from the block
cache.

Repack merges runs into a multi-pack index. `git-server`'s load test showed
why that matters: per-request cost grows linearly with the number of live
packs.

Filters cost about 1.25 MiB per million objects, so repositories of up to a
few hundred thousand objects keep every filter in RAM. Larger repositories
still work, with more card reads.

### Commit graph

Each repository has a commit-graph table on the card that records each
commit's object ID, its parents as table positions, its generation number,
its root tree, and its commit time. Pushes append to it and repack merges it.
Fetch negotiation, fast-forward checks, and connectivity checks read it
instead of inflating commit objects.

### Caches

- The object cache holds inflated commits, trees, and recently pushed blobs.
  A thin push's deltas usually point at the previous version of each changed
  file, which is often still cached.
- The block cache holds compressed pages for fetch responses and index pages.
- Pushes write through both caches. A common CI pattern, one push followed by
  many runners fetching it, is served from RAM.

### Delta-chain cap

A thin push stores each new version of a file as a delta against the old
version, so the newest version of a busy file ends up at the end of the
longest chain. Git's own packs order chains the other way, and git restores
that order during `gc` by searching for new deltas, which the device can't
afford. Instead, maintenance caps chains. When an object's chain grows past a
limit, for example 50, maintenance writes the object out in full and points
the index at the full copy. The full copy uses zlib's uncompressed blocks, or
a fast compressor in the background if storage matters more. Reads of the
newest version then stay cheap.

## Push path

Push uses the v0 receive-pack protocol, because protocol v2 doesn't support
push:

1. `GET /<repo>/info/refs?service=git-receive-pack` returns a ref
   advertisement from RAM.
2. `POST /<repo>/git-receive-pack` carries ref-update commands followed by
   the pack.

Git's [`remote-curl.c`][remote-curl] sets these HTTP details:

- A body that fits in `http.postBuffer`, 1 MiB by default, arrives with
  `Content-Length`.
- A larger body arrives with chunked transfer encoding, after a probe POST
  whose body is the 4-byte flush packet `0000`. The server must answer the
  probe without treating it as a push.
- Once credentials are involved, git sends `Expect: 100-continue` with large
  bodies. The server answers `100 Continue` at once. Otherwise, curl waits
  about a second before it sends the body.
- ESP-IDF's `esp_http_server` [treats a chunked request body as
  empty][httpd-parse], so the firmware has its own HTTP/1.1 parser.

The server advertises `report-status`, `report-status-v2`, `delete-refs`,
`side-band-64k`, `quiet`, `atomic`, `ofs-delta`, `object-format=sha1`, and
`agent`. It accepts thin packs by default because they save radio time and
storage. A configuration option [advertises `no-thin`][caps], which makes
clients send full objects instead.

### Ingest

- A small push, with a body of up to 256 KiB, is buffered in PSRAM, indexed in
  memory, and committed in one log block together with its pack.
- A large push writes its bytes to its own pack segments as they arrive, in
  64 KiB DMA writes. The scanner reads from an in-RAM ring buffer while it
  keeps up, and from the copy on the card when it falls behind, so a slow
  scan never closes the TCP window. If the card is slower than Wi-Fi, as in
  SPI mode, the server stops reading the socket instead, and TCP flow control
  slows the client.

One large push indexes at a time. Others keep receiving to the card and wait.
Small pushes don't wait behind a large one, because the index worker handles
them between chunks of a large scan.

If a client disconnects, or a push fails validation, its segments go back to
the free list. No commit record references them, so recovery ignores them
too.

### Scanner

The scanner follows `git-server`'s incremental `PackScanner`, with these
changes for the device:

- One inflater per worker, reset between entries.
- A ring buffer instead of draining a `Vec` from the front.
- No Adler-32 checks. The pack's trailing SHA-1 covers transport errors, and
  every object gets hashed anyway.
- Hardware SHA-1 for the pack trailer and for every object.

### Rebuilding deltas while the pack arrives

During the scan, the worker keeps the inflated content of every entry that
has delta children in a byte-budgeted cache. When a delta arrives and its base
is cached, the worker rebuilds and hashes it at once, and it drops a base when
the base's last child is done. Objects whose base fits in the SRAM arena
rebuild at internal-RAM copy speed instead of PSRAM speed.

In a simulation with a 2 MiB cache, 99.9 percent of the deltas in the
400-commit pack rebuild as they arrive, so such a push finishes almost as soon
as its last byte lands. Full-history imports defer more: about half of
ripgrep's deltas with a 2 MiB cache, and 15 percent with 8 MiB.

A second pass handles deferred deltas. It groups them by the root of their
chain and walks each chain tree depth first from the root, holding only the
current path in memory. It reads compressed deltas from the card, or from a
PSRAM spill buffer when they fit.

Thin-pack bases come from the store, usually from the object cache.

### Validation, commit, and reply

- Each new ref target must exist, and a commit's root tree must be present,
  which is `git-server`'s rule. Force pushes are allowed by default, as in
  git. A per-repository setting can reject non-fast-forward updates, checked
  with the commit graph.
- While indexing, the server sends side-band progress messages and, every few
  seconds, keepalive packets, which matches git's `receive.keepAlive`
  behavior.
- report-status goes out after the grouped commit is on the card.

Limits protect the device from damaged or hostile packs: a maximum declared
object size, a maximum rebuilt size that's checked before allocating, a
maximum chain depth, a maximum number of objects per push, a maximum number of
concurrent pushes, and an optional maximum push size.

## Fetch path

Fetch uses protocol v2 only, as `git-server` does. Git has used protocol v2 by
default since version 2.26.

- `GET /<repo>/info/refs?service=git-upload-pack` returns fixed capability
  bytes.
- The server caches `ls-refs` responses by repository state and request
  arguments, so an up-to-date `git fetch` never touches the card.
- Git gzips fetch request bodies larger than 1 KiB, so the server inflates
  them with the same decoder it uses for packs.

The server handles a `fetch` request in four steps:

1. **Negotiation in one round trip.** The server acknowledges the common
   `have` lines and sends `ready` with the pack in the same response.
2. **Object selection.** The planner walks commits from the wants through the
   commit graph and stops at ancestors of the common haves. It compares the
   trees of new commits with the trees of boundary commits and skips
   unchanged subtrees, as `git-server` does. Objects in boundary trees count
   as already on the client.
3. **Emission.** Each object's stored compressed bytes go out unchanged. A
   delta whose base is also being sent, or is already on the client, goes out
   as a delta. A delta whose base the client lacks is rebuilt and sent whole,
   wrapped in zlib's uncompressed blocks, so the device never runs a
   compressor. Objects go out in pack-offset order for card locality, and the
   trailing SHA-1 comes from the hardware engine.
4. **Full clones.** A fetch with no haves that wants every ref streams the
   consolidated packs unchanged, with a new header and trailer, and skips
   selection. The server uses this path only for packs that garbage
   collection has confirmed hold only reachable objects, so a force-pushed
   secret never reaches a new clone.

A response cache makes repeated fetches cheap. Its key is a hash of the
wants, the common haves that aren't ancestors of other common haves, and the
request options. CI runners that are one push behind send requests with the
same key, so the first request builds the pack and the rest replay it, from
PSRAM for responses of up to 256 KiB and from a spill segment beyond that.
Entries never go stale, because objects never change and wants are object
IDs, so the cache evicts only the least recently used entries.

## Networking

- The HTTP/1.1 server runs on non-blocking lwIP sockets in the net loop, with
  keep-alive.
- Clients close connections first, so TIME_WAIT state lands on the client
  instead of occupying the ESP32's TCP control blocks for 120 s. On errors,
  the server closes with `SO_LINGER` set to 0, which sends a reset.
- Wi-Fi power save is off (`WIFI_PS_NONE`). Modem sleep delays incoming
  packets by up to a beacon interval, about 100 ms.
- AMPDU aggregation and the Wi-Fi and lwIP IRAM options are on. TCP windows
  and send buffers start at 32 KiB and shrink as the number of concurrent bulk
  connections grows, as Espressif's tuning guide recommends.
- `LWIP_MAX_SOCKETS` is 32 to 64, and `LWIP_MAX_ACTIVE_TCP` is 64 or more.
  The lwIP task runs on core 0.
- The device announces an mDNS name, such as `gitbox.local`, so clients can
  use `http://gitbox.local/REPO`.

## Security

- **Default.** HTTP on a private network. Clients authenticate with HTTP Basic
  auth and per-user tokens. Tokens and per-repository read and write lists
  live in NVS and are provisioned over USB, as in `inkbot-esp32/`. Tokens
  cross the network in clear text, so anyone who can capture traffic on the
  network can read them.
- **Optional HTTPS.** mbedTLS with an ECDSA P-256 certificate and session
  tickets. Each `git` command still pays a full handshake of about 2 s, which
  limits the device to about one operation per second. Use HTTPS when
  confidentiality matters more than throughput, or run a TLS-terminating proxy
  on the network.
- **Hostile input.** Besides the push limits, the server caps connections per
  client address and checks each object's inflated size against its declared
  size.

## Status and observability

- `GET /api/status` returns JSON with free SRAM and PSRAM, card write latency
  percentiles, queue depths, and per-operation counters and latencies.
- Every response carries a `Server-Timing` header with per-phase times, as in
  `git-server`.
- Logs go to the serial console and, optionally, to the FAT partition.

## Rust implementation

### Framework

| | `esp-idf-svc` on ESP-IDF | `esp-hal`, `esp-radio`, and `embassy-net` |
|---|---|---|
| SD host driver | ESP-IDF SDMMC driver, mature | Initial driver, added in `esp-hal` 1.2.0 in September 2026 |
| Wi-Fi and TCP | lwIP, with published and tunable throughput | smoltcp, with less published data |
| SHA engine | mbedTLS and `esp_sha`, with DMA | `esp-hal` SHA driver |
| Concurrency | FreeRTOS tasks and `poll` | Async executors |
| Precedent in this repository | `inkbot-esp32/` and `esp32-ble/` | None |

The design uses `esp-idf-svc`. Milestone 0 can revisit the choice if the
bare-metal stack measures faster.

### Crate layout

The new crate, `git-esp32/`, follows `inkbot-esp32/`:

- `src/lib.rs` is the host-testable core, with no ESP-IDF dependency. It holds
  pkt-line framing, the HTTP parser with chunked bodies and gzip, receive-pack
  and v2 upload-pack, the pack scanner, delta code, and emitter, the store
  format with commits, recovery, index runs, and the commit graph over a
  `BlockDevice` trait, the caches, and maintenance.
- `src/main.rs` builds only with the `firmware` feature. It holds Wi-Fi setup,
  the SDMMC `BlockDevice`, a hardware SHA-1 implementation, NVS
  configuration, OTA, and task setup.
- `tools/` holds a host binary that serves a card image or a card in a USB
  reader with the same core, for debugging, recovery, and export.

The root `AGENTS.md` says that Rust apps don't import each other, so the port
copies and adapts code from `git-server/`: pkt-line framing, the object model,
delta application, the scanner with the changes listed earlier, the protocol
handlers, fetch selection, emission, and repack. It leaves out the R2,
Durable Object, and KV glue, the JSON state document, the file-log and blame
APIs, and the async `Store` trait.

Build details:

- The target is `xtensa-esp32s3-espidf`, built with `cargo +esp` and
  `-Z build-std`, like `inkbot-esp32/`. ESP-IDF releases after 5.2 bounce
  non-DMA SD buffers in multi-block chunks instead of single blocks, which is
  worth having even though the store avoids that path.
- The partition table has `nvs`, `otadata`, `phy_init`, two OTA slots, and a
  core dump partition.
- OTA can reuse `inkbot-esp32/`'s signed GHCR images later.
- CI gets a `git-esp32.yml` workflow for host tests and the Xtensa build, and
  the directory is excluded from `test.yml` discovery, like `inkbot-esp32/`
  and `esp32-ble/`. The root `AGENTS.md` and `README.md` gain entries when the
  code lands.

## Testing

- **Host integration.** Real `git clone`, `fetch`, `push`, and `fsck` run
  against the core over localhost with a file-backed `BlockDevice`, following
  `git-server`'s integration tests.
- **Power cuts.** A `BlockDevice` cuts power at a random write, dropping or
  tearing the write in flight and optionally damaging a neighboring page, then
  restarts the store. Every acknowledged push must survive, every ref must
  point at a complete object graph, and `git fsck` must pass on a fresh clone.
- **Memory.** A tracking allocator enforces the SRAM and PSRAM budgets,
  following `git-server`'s `tests/memory.rs`.
- **Slow cards.** Injected write stalls of 100 to 500 ms exercise grouped
  commits and keepalives.
- **Device.** Benchmark firmware for milestone 0, soak tests, and load tests
  modeled on `git-server`'s load test, with writers on separate branches and
  readers cloning, reporting operations per second and p50 and p95 latency.

## Milestones

0. **Hardware benchmarks.** Firmware that measures, on the target board and
   card: TCP throughput in the target room, raw SD sequential and random
   reads and writes with DMA buffers, inflate speed on real git objects with
   `miniz_oxide`, the ROM inflater, and a libdeflate-style decoder, hardware
   SHA-1, PSRAM copies, and TLS handshake time. The results replace every
   *estimated* number in this document.
1. **Host core.** The store, receive-pack, and v2 fetch over a file-backed
   block device, with real-git and power-cut tests.
2. **Firmware bring-up.** Wi-Fi, the SD block device, the net loop, and small
   pushes and fetches on the board, with the memory budget measured.
3. **Large pushes.** Delta rebuilds during the scan, the second pass, progress
   and keepalives, and indexing speed compared with this document.
4. **Request rate.** Response caches, the full-clone path, and a load test.
5. **Maintenance.** Repack, the chain cap, garbage collection, and
   checkpoints, plus a long soak with power cuts.
6. **Hardening.** Auth, optional HTTPS, OTA, the status endpoint, and docs.

## Risks and open questions

- Inflate speed is an estimate. If it measures under 2 MB/s, large source
  pushes slow down in proportion. Possible fixes are running the decoder from
  IRAM, caching the fixed Huffman tables, a libdeflate-style decoder, or an
  ESP32-P4.
- Internal SRAM is tight. Wi-Fi buffers compete with SD DMA buffers and the
  inflater.
- Cards differ in how they behave when power fails. Consumer cards can damage
  acknowledged data, so anything important needs an industrial card.
  Mirroring commit records to a second segment is an option.
- The request-rate estimates assume a clean channel and a strong signal. A
  busy 2.4 GHz band can cut them several times over.
- Pushes of more than about 200,000 objects need a spill-to-SD mode, or need
  to be split.
- With plain HTTP, anyone on the network can read the tokens.
- The store format is custom. The host tool and bundle exports reduce the
  risk of losing access to data.

## Appendix: how the indexing numbers were measured

A throwaway Rust program linked `git-server` as a path dependency and ran its
`PackScanner` and `resolve_pack` over each pack on an Intel Xeon host with
Rust 1.99.0. The program also simulated rebuilding deltas during the scan,
with a byte-budgeted cache that drops a base after its last child, and
callgrind counted instructions in the scan phase. The packs were a bare clone
of `github.com/BurntSushi/ripgrep`, this repository's full pack, and the output
of `git pack-objects --revs` for `HEAD ^HEAD~400` in this repository. The
device estimates scale these counts with the published hardware figures, and
milestone 0 replaces them.

[wifi-perf]: https://github.com/espressif/esp-idf/blob/master/docs/en/api-guides/wifi-driver/wifi-performance-and-power-save.rst
[sd-issue]: https://github.com/espressif/esp-idf/issues/11628
[sd-msc]: https://github.com/atomic14/esp32-sdcard-msc
[sdmmc-522]: https://github.com/espressif/esp-idf/blob/v5.2.2/components/sdmmc/sdmmc_cmd.c
[drorgl]: https://github.com/drorgl/esp32-sd-card-benchmarks
[perf-s3]: https://github.com/espressif/esp-idf/blob/release/v5.4/components/idf_test/include/esp32s3/idf_performance_target.h
[memcopy]: https://github.com/project-x51/esp32-s3-memorycopy
[https-server]: https://github.com/espressif/esp-idf/blob/master/docs/en/api-reference/protocols/esp_https_server.rst
[lwip-kconfig]: https://github.com/espressif/esp-idf/blob/release/v5.4/components/lwip/Kconfig
[remote-curl]: https://github.com/git/git/blob/master/remote-curl.c
[httpd-parse]: https://github.com/espressif/esp-idf/blob/release/v5.4/components/esp_http_server/src/httpd_parse.c
[caps]: https://github.com/git/git/blob/master/Documentation/gitprotocol-capabilities.adoc
