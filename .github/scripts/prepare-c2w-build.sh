#!/usr/bin/env bash
# Prepare the build inputs for a container2wasm (c2w) conversion.
#
# c2w drives the whole conversion from a Dockerfile it embeds in its own
# binary, and that Dockerfile fetches its inputs from the network while the
# build runs. Two of those fetches are unreliable enough to sink a build that
# otherwise takes hours:
#
#   * The build assets are git-cloned from the project's old home
#     (github.com/ktock/container2wasm), which no longer carries the release
#     tags, so every conversion dies on "Remote branch v0.8.4 not found". We
#     skip the clone entirely by handing buildx a local checkout of the
#     matching release as the `assets` build context (`c2w --assets`).
#   * zlib is fetched from zlib.net/fossils, which answered a GitHub runner
#     with a non-tarball that reached tar as "gzip: stdin: not in gzip
#     format". zlib's own GitHub release carries a byte-identical tarball, so
#     use that.
#
# Writes two files into the current directory, for `c2w --assets` and
# `c2w --dockerfile` respectively:
#
#   c2w-src/         the pinned container2wasm source tree
#   Dockerfile.c2w   that release's Dockerfile, patched as described above
#
# Usage: prepare-c2w-build.sh <c2w version tag>   (e.g. v0.8.4)
set -euo pipefail

version="${1:-${C2W_VERSION:-}}"
if [ -z "$version" ]; then
  echo "usage: prepare-c2w-build.sh <c2w version tag>" >&2
  exit 2
fi

curl -fsSL --retry 5 --retry-delay 5 -o c2w-src.tar.gz \
  "https://github.com/container2wasm/container2wasm/archive/refs/tags/${version}.tar.gz"
rm -rf c2w-src
mkdir c2w-src
tar -xzf c2w-src.tar.gz -C c2w-src --strip-components=1

# Take the Dockerfile from the binary rather than from the source tree, so the
# patched copy is exactly what this c2w build expects.
c2w --show-dockerfile > Dockerfile.c2w

python3 - <<'PY'
import pathlib
import re

path = pathlib.Path("Dockerfile.c2w")
text = path.read_text()

zlib_from = (
    "RUN curl -LsS https://zlib.net/fossils/zlib-$ZLIB_VERSION.tar.gz"
    " | tar zxC /zlib --strip-components=1"
)
zlib_to = (
    "RUN curl -fsSL"
    " https://github.com/madler/zlib/releases/download/v$ZLIB_VERSION/zlib-$ZLIB_VERSION.tar.gz"
    " | tar zxC /zlib --strip-components=1"
)
if zlib_from not in text:
    raise SystemExit(
        "c2w's Dockerfile no longer fetches zlib the way this patch expects; "
        "re-check prepare-c2w-build.sh against the pinned c2w release."
    )
text = text.replace(zlib_from, zlib_to)

# Retry the remaining downloads too. Anchoring on "RUN " keeps the rewrite off
# the apt-get lines that merely install curl and wget.
text = re.sub(r"^RUN curl -", "RUN curl --retry 5 --retry-delay 5 -", text, flags=re.M)
text = re.sub(r"^RUN wget ", "RUN wget --tries=5 --waitretry=5 ", text, flags=re.M)

path.write_text(text)
PY

echo "Prepared $(realpath c2w-src) and $(realpath Dockerfile.c2w) for c2w ${version}."
