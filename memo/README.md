# memo

memo runs a command, records what it read, and replays the command's output
until those inputs change. It's a variation on
[once](https://github.com/alex0ptr/once), which caches output for a fixed
time. memo checks the files, directories, and HTTP responses that the command
actually used.

```sh
memo -- python3 report.py   # runs report.py and records what it read
memo -- python3 report.py   # replays the output: nothing it read changed
vi data.csv
memo -- python3 report.py   # runs again
```

memo runs on Linux (x86_64 and aarch64) with kernel 5.5 or later. Kernel 6.6
or later traces faster.

## Build

```sh
cd memo
cargo build --release
install target/release/memo ~/.local/bin/
```

## Usage

```
memo [OPTIONS] [--] COMMAND [ARGS...]
memo explain [OPTIONS] [--] COMMAND [ARGS...]
memo clear
```

| Option | Meaning |
| --- | --- |
| `--ttl DURATION` | Expire results after `DURATION` (for example `90s`, `30m`, `12h`, or `7d`), and cache runs whose network access memo can't check. |
| `--http` | Record HTTP and HTTPS requests through a local proxy and check them again before replaying. See [HTTP requests](#http-requests). |
| `--refresh` | Run the command even if a cached result applies. |
| `--cache-failures` | Cache and replay runs that exit with a nonzero status. |
| `--ignore PATH` | Don't record files under `PATH`. Repeatable. |
| `--ignore-env NAME` | Leave environment variable `NAME` out of the cache key. Repeatable. |
| `-v`, `--verbose` | Report hits, misses, and why a run wasn't cached. |

`memo explain -- COMMAND` reports whether a cached result would be replayed
and, if not, which inputs changed. It exits 0 if a result would be replayed.
`memo clear` deletes all cached results.

Results live in `$MEMO_CACHE_DIR`, or in `memo` under `$XDG_CACHE_HOME` or
`~/.cache`.

## What memo records

The cache key is the command line, the working directory, the environment,
what standard input is, whether standard output and error are terminals, and
the `--ignore` and `--http` options. memo can't see a program read an
environment variable, so every variable is part of the key except a few that
differ between terminals, such as `OLDPWD`, `SHLVL`, and `SSH_TTY`. To leave
out others, use `--ignore-env`.

For each run, memo records the following:

- **Inputs.** Content the command read, including the program, its shared
  libraries, and the script interpreter or ELF loader that the kernel opens.
  Metadata it queried with `stat` or `access`. Directories it listed. Paths it
  looked for and didn't find, such as earlier `PATH` entries and optional
  config files.
- **Outputs.** Files and directories it created, changed, renamed, or
  deleted, in the state it left them.
- **Its output and exit status.** Standard output and error, in the order the
  command wrote them.

A later call replays the result if every input is unchanged and every output
is still as the run left it. If you delete an output, the next call runs the
command again and recreates it. memo keeps up to four results for each key,
so switching back and forth between two git branches can hit for both.

memo compares content with BLAKE3 hashes. A lookup runs `stat` on each
recorded path and hashes a file again only if its size, inode, mtime, or
ctime changed. When a command runs `stat` on a file, the modification time
counts as an input, so `touch` causes a rerun even if the content is the
same.

## When memo doesn't cache

`memo -v` reports why a run wasn't cached. memo doesn't cache a run that does
any of the following:

- Changes a file it read, such as appending to a log or incrementing a
  counter. A rerun would see different input. A command that creates entries
  in a directory it lists becomes cacheable on its next run.
- Reads a file that something else changes while it runs.
- Connects to a network address, or to the Unix socket of another process
  such as a daemon. memo can't tell whether the answer would change. With
  `--http`, HTTP requests can be checked; with `--ttl`, the rest are cached
  for a fixed time.
- Reads standard input from a terminal or a pipe. Redirect from a file
  instead (`memo -- jq . < in.json`), and memo records the file.
- Exits with a nonzero status, unless you pass `--cache-failures`, or is
  killed by a signal.
- Leaves background processes running. memo doesn't wait for them, and a
  forked helper keeps answering their traced calls until they exit.
- Changes mounts or namespaces, or runs a 32-bit program.
- Prints more than 64 MiB.

Some tools rewrite bookkeeping files on every run. memo ignores Go's
telemetry counters (`~/.config/go/telemetry`) and npm's debug logs
(`~/.npm/_logs`). For other files like these, use `--ignore`.

memo assumes that a command's output depends only on what memo records. It
doesn't see reads of the clock, random numbers, or process IDs, so don't use
it for commands like `date`.

## HTTP requests

With `--http`, memo runs a proxy on a loopback port while the command runs,
and points the command at it with `http_proxy`, `https_proxy`, and the CA
bundle variables that common clients read: `SSL_CERT_FILE`,
`CURL_CA_BUNDLE`, `REQUESTS_CA_BUNDLE`, `NODE_EXTRA_CA_CERTS`,
`GIT_SSL_CAINFO`, and a few more. HTTPS goes through a certificate authority
that memo creates for the run and that only the wrapped command trusts. curl,
Python, and Go programs work this way.

memo records each GET and HEAD request with the response's `ETag` and
`Last-Modified` and a hash of its body. Before replaying a result, it checks
each response:

1. If the response had an `ETag` or `Last-Modified`, memo sends `HEAD` with
   `If-None-Match` and `If-Modified-Since`. A `304 Not Modified`, or a `2xx`
   response with the same validators, means unchanged. A different `ETag`
   means changed. Neither answer includes the body.
2. If the response had no validators, or the server refuses `HEAD` or
   answers it without validators, memo repeats the GET and compares the
   response with the recorded hash.

memo uses `If-None-Match`, not `If-Match`. `If-Match` compares entity tags
strongly, so a weak tag such as `W/"abc"` never matches, even when nothing
changed. Servers also don't all evaluate `If-Match` on reads: proxy.golang.org
answers `HEAD` with `If-Match: "stale"` with `200`. For the same reason, memo
compares the validators in a `2xx` response itself, so a server that ignores
conditional headers can't make memo replay a changed response.

Requests with other methods count as network access that memo can't check.
The proxy accepts only clients that send a password created for the run, and
it doesn't chain to an existing `HTTPS_PROXY`. Clients that ignore the proxy
variables, such as `fetch` in Node.js 22, connect directly, and memo records
that as network access it can't check.

## How it works

memo installs a seccomp filter in the child before `exec`, and the command's
descendants inherit it. The filter returns `SECCOMP_RET_USER_NOTIF` for file,
exec, directory-listing, socket, and mount system calls. A memo thread reads
each call's arguments from the blocked thread's memory, records the state of
the path before the call takes effect, and answers
`SECCOMP_USER_NOTIF_FLAG_CONTINUE`, so the call then runs unchanged. Other
system calls never leave the kernel.

- `io_uring_setup` fails with `ENOSYS`, as it does in many container
  runtimes, because io_uring file operations bypass system calls. libuv, and
  so Node.js, falls back to ordinary calls.
- On Linux 6.6 and later, memo turns on synchronous wake-up while the command
  traps one call at a time, which cuts the cost of a trapped call from about
  11 µs to 4 µs. memo turns it off once calls from several threads queue up.
- memo is a child subreaper, so orphaned descendants stay its children and
  memo knows when the last one exits.
- If memo's standard output or error is a terminal, the command gets a
  pseudo-terminal, so it keeps its colors and line buffering.
- The filter requires `no_new_privs`, so setuid programs such as `sudo` don't
  gain privileges under memo.

## Performance

The following table shows the median of seven runs of each command run
plainly, under `memo --refresh` (traced and recorded every time), and as a
cache hit. The machine is an 8-core VM with Linux 6.12.

| Command | Plain | Recorded | Replayed | Inputs |
| --- | ---: | ---: | ---: | ---: |
| `npm test` in `qr-quine/` | 364 ms | 409 ms | 2.7 ms | 827 |
| `make -B -j8` with 201 C files | 555 ms | 773 ms | 3.3 ms | 505 |
| `go vet ./...` in `kube/` | 109 ms | 286 ms | 15.5 ms | 9,874 |
| `cargo build` with nothing to do | 38 ms | 52 ms | 2.5 ms | 453 |
| `python3 script.py` | 17.5 ms | 23.3 ms | 1.8 ms | 108 |
| `node script.js` | 17.5 ms | 22.5 ms | 1.2 ms | 17 |
| `rg -c func kube` | 4.6 ms | 15.3 ms | 2.5 ms | 661 |
| `git status` in this repository | 7.0 ms | 70.4 ms | 5.5 ms | 4,142 |

memo pays off when a command does much more work than checking its inputs.
`git status` is already incremental, and it calls `stat` on every file from
several threads, which one memo thread answers in turn. Recording it costs 10
times as much as running it.

## Limitations

- memo runs only on Linux. macOS has no unprivileged way to intercept
  another program's system calls: `DYLD_INSERT_LIBRARIES` doesn't reach
  protected binaries such as `/bin/sh`, and the Endpoint Security framework
  needs an entitlement from Apple.
- One thread answers every trapped call, so commands that trap calls from
  many threads at once slow down the most.
- A command that talks to a daemon, such as Docker, Gradle, or sccache, can
  be cached only with `--ttl`.
- If memo runs inside another memo, the inner one can't add its own filter
  and runs the command without its cache.

## Security

The cache holds command output and, with `--http`, request header fields,
which can include credentials. memo creates the cache directory with mode
`0700` and its files with mode `0600`.

## Test

```sh
cd memo
cargo test
```

The end-to-end tests run real commands under memo: `sh`, `cat`, `ls`, `bash`,
`python3`, and `curl`, plus `script` from util-linux for the terminal test.

## Related tools

Go's test cache works this way inside one program: `go test` logs the files
and environment variables that a test reads, and reuses the result while they
stay the same. Build tools have traced commands to find dependencies:
[fabricate](https://github.com/brushtechnology/fabricate) uses `strace`,
[Rattle](https://github.com/ndmitchell/rattle) uses `fsatrace`, and
[Riker](https://codeberg.org/curtsinger/riker) traces the system calls of a
build. [bkt](https://github.com/dimo414/bkt) caches command output for a fixed
time and can watch files that you name.
