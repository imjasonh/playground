# repro

Checks a Litestream version for
[benbjohnson/litestream#1018](https://github.com/benbjohnson/litestream/issues/1018).
It writes through the write-enabled VFS, then runs `PRAGMA integrity_check`
in the writer and from a fresh read-only VFS, and counts the rows a new
instance sees. It prints `PASS` or `FAIL`.

This is its own module so that it can pin any Litestream version without
changing the server's. It needs CGO and the `vfs` build tag:

```bash
go run -tags vfs . -replica-url file:///tmp/repro-1 -c 1 -duration 30s
go run -tags vfs . -replica-url file:///tmp/repro-10 -c 10 -duration 60s
go run -tags vfs . -replica-url file:///tmp/repro-compact -c 4 -duration 130s -compaction
```

Use a new replica path for each run. To test another release or an unmerged
commit, change the required version first:

```bash
go get github.com/benbjohnson/litestream@v0.5.18
go get github.com/benbjohnson/litestream@COMMIT
```

Replace `COMMIT` with a commit hash from `benbjohnson/litestream`. For a
pull request from a fork, add a `replace` directive that points at the fork's
module and commit instead.
