#!/usr/bin/env bash
# Empirically test whether Cloudflare's request-body cap actually binds git
# pushes, which use Transfer-Encoding: chunked for bodies >1 MB.
#
#   GIT_SERVER_URL=https://git.<account>.workers.dev ./scripts/probe-body-limit.sh
#
# Background (docs/design.md "Size limits"): Cloudflare documents a plan-based
# request-body cap (100 MB Free/Pro) enforced at the edge with a 413. That
# enforcement historically relied on the edge *buffering* uploads; Cloudflare's
# 2025 core-proxy rollout switched uploads to streaming, and projects (e.g.
# Gitea's LFS chunked-upload change) report that chunked bodies now pass. This
# probe settles it for *this* deployment:
#
#   test A (control): POST with explicit Content-Length ~120 MB
#       -> 413 = edge cap enforced on declared sizes (expected)
#   test B (hypothesis): same body, Transfer-Encoding: chunked (like git push)
#       -> HTTP 200 + our own "per-push limit" report-status = the edge
#          streamed >100 MB into the Worker; the documented cap does NOT bind
#          chunked git pushes (our server-side PUSH_LIMIT_BYTES is what fired,
#          after counting 100 MB of received body)
#       -> 413 / connection cut ≈ the edge cap still binds
#
# The body is a syntactically valid receive-pack request (command pkt-line +
# flush + a pack whose first entry is a ~120 MB incompressible blob), so the
# server keeps reading — and counting — instead of rejecting early. The target
# ref is bogus-but-valid; even if a server accepted the body, the pack is
# truncated (no trailer) and the push cannot apply.

set -euo pipefail
cd "$(dirname "$0")/.."

: "${GIT_SERVER_URL:?set GIT_SERVER_URL to the deployed worker, e.g. https://git.<acct>.workers.dev}"
PROBE_MB="${PROBE_MB:-120}"
REPO="probe-limit-$(date +%s)"
URL="$GIT_SERVER_URL/$REPO/git-receive-pack"

BODY="$(mktemp)"
trap 'rm -f "$BODY"' EXIT

echo "==> building a ~${PROBE_MB} MB valid receive-pack body"
python3 - "$BODY" "$PROBE_MB" <<'EOF'
import os, struct, sys, zlib

out_path, mb = sys.argv[1], int(sys.argv[2])
target_bytes = mb * 1024 * 1024

def pkt(s: str) -> bytes:
    return f"{len(s) + 4:04x}{s}".encode()

with open(out_path, "wb") as out:
    # Command section: create a ref (oids need only be well-formed).
    cmd = f"{'0'*40} {'1'*40} refs/heads/probe\0report-status agent=probe"
    out.write(pkt(cmd))
    out.write(b"0000")

    # Pack header: version 2, one entry.
    out.write(b"PACK" + struct.pack(">II", 2, 1))

    # Entry header: type=blob(3), huge size, MSB-continued varint.
    size = target_bytes * 2  # inflated size claim; stream is truncated anyway
    hdr = bytearray()
    b = (3 << 4) | (size & 0x0F)
    size >>= 4
    while size:
        hdr.append(b | 0x80)
        b = size & 0x7F
        size >>= 7
    hdr.append(b)
    out.write(bytes(hdr))

    # ~target_bytes of zlib-compressed incompressible data, streamed.
    comp = zlib.compressobj(0)  # level 0: stored blocks, output ~= input
    written = 0
    rng = os.urandom(64 * 1024)
    while written < target_bytes:
        chunk = comp.compress(rng)
        out.write(chunk)
        written += len(chunk)
    # No flush/trailer: the pack is deliberately truncated.

print(f"body: {os.path.getsize(out_path) / 1e6:.1f} MB", file=sys.stderr)
EOF

run() {
  local label="$1"; shift
  echo
  echo "==> $label"
  local code
  code=$(curl -sS -m 300 -o /tmp/probe-resp.bin -D /tmp/probe-hdr.txt \
    -w '%{http_code}' -X POST \
    -H 'Content-Type: application/x-git-receive-pack-request' \
    "$@" --data-binary @"$BODY" "$URL" || echo "curl-failed")
  echo "    HTTP status: $code"
  tr -d '\r' < /tmp/probe-hdr.txt | grep -i '^server-timing:' | head -1 | sed 's/^/    /' || true
  # Decode enough of the response to recognize our report-status text.
  if strings /tmp/probe-resp.bin 2>/dev/null | grep -q "per-push limit"; then
    echo "    body contains OUR size-limit report -> >100 MB traversed the edge"
  elif [ "$code" = "413" ]; then
    echo "    413 -> rejected by the Cloudflare edge (cap enforced)"
  else
    echo "    body starts: $(head -c 120 /tmp/probe-resp.bin | strings | head -2 | tr '\n' ' ')"
  fi
}

# Test A (control): declared size. The edge knows the size upfront.
run "test A: Content-Length declared (control; docs say 413)"

# Test B (hypothesis): chunked, exactly how git sends pushes >1 MB.
# curl uses chunked encoding when told to send from stdin-like sources with
# no length; -H drops the auto Content-Length.
run "test B: Transfer-Encoding chunked (how git pushes)" \
  -H 'Transfer-Encoding: chunked'

echo
echo "Interpretation:"
echo "  A=413, B=our-report  -> cap only binds declared Content-Length; real"
echo "                          git pushes (chunked) are NOT capped at the edge;"
echo "                          effective limit is our PUSH_LIMIT_BYTES config"
echo "  A=413, B=413/cut     -> cap binds everything; LFS/presigned-upload is"
echo "                          the only way past it"
