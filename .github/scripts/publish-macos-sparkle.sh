#!/usr/bin/env bash
# Publish a macOS Sparkle update from fastlane beta artifacts.
#
# Expects cwd or RELEASE_DIR to contain sparkle-metadata.json produced by
# hello-macos fastlane beta, plus the enclosure zip. Then:
#   1. Creates / uploads a GitHub Release asset (enclosure)
#   2. Updates gh-pages/<feed_path> appcast.xml to point at that asset
#
# Usage (CI, after fastlane beta):
#   RELEASE_DIR=hello-macos/fastlane/release \
#   REPO=owner/name \
#   GH_TOKEN=... \
#   bash .github/scripts/publish-macos-sparkle.sh
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

release_dir="${RELEASE_DIR:?RELEASE_DIR must point at fastlane/release}"
meta_file="$release_dir/sparkle-metadata.json"
: "${REPO:?REPO must be owner/name}"
: "${GH_TOKEN:?GH_TOKEN required to create releases and push gh-pages}"

if [[ ! -f "$meta_file" ]]; then
  echo "No sparkle-metadata.json in $release_dir — nothing to publish." >&2
  exit 1
fi

if ! command -v jq >/dev/null; then
  echo "jq is required" >&2
  exit 1
fi

app=$(jq -r .app "$meta_file")
title=$(jq -r .title "$meta_file")
marketing=$(jq -r .marketing_version "$meta_file")
build=$(jq -r .build_version "$meta_file")
enclosure=$(jq -r .enclosure "$meta_file")
enclosure_path=$(jq -r .enclosure_path "$meta_file")
ed_signature=$(jq -r .ed_signature "$meta_file")
feed_path=$(jq -r .feed_path "$meta_file")

if [[ ! -f "$enclosure_path" ]]; then
  echo "Enclosure missing: $enclosure_path" >&2
  exit 1
fi

length=$(wc -c < "$enclosure_path" | tr -d ' ')
tag="${app}-v${marketing}"
# Stable Pages URL for the feed; enclosure URL is the Release asset.
owner="${REPO%%/*}"
repo_name="${REPO#*/}"
pages_feed_url="https://${owner}.github.io/${repo_name}/${feed_path}"

echo "Publishing $tag ($title), enclosure=$enclosure ($length bytes)"

# --- GitHub Release ----------------------------------------------------------
if gh release view "$tag" --repo "$REPO" >/dev/null 2>&1; then
  echo "Release $tag already exists; uploading/replacing asset."
  gh release upload "$tag" "$enclosure_path" --repo "$REPO" --clobber
else
  gh release create "$tag" "$enclosure_path" \
    --repo "$REPO" \
    --title "$title" \
    --notes "Automated macOS Sparkle build ${marketing} (${build})."
fi

asset_url=$(gh release view "$tag" --repo "$REPO" --json assets \
  --jq ".assets[] | select(.name==\"$enclosure\") | .url")
# gh API "url" is the API URL; browsers/Sparkle need the browser_download_url.
browser_url=$(gh api "repos/${REPO}/releases/tags/${tag}" \
  --jq ".assets[] | select(.name==\"$enclosure\") | .browser_download_url")

if [[ -z "$browser_url" ]]; then
  echo "Could not resolve browser_download_url for $enclosure" >&2
  exit 1
fi
echo "Enclosure URL: $browser_url"

# --- appcast on gh-pages -----------------------------------------------------
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

git clone --depth 1 --branch gh-pages \
  "https://x-access-token:${GH_TOKEN}@github.com/${REPO}.git" "$work/gh-pages"

feed_dir="$work/gh-pages/$(dirname "$feed_path")"
mkdir -p "$feed_dir"
feed_file="$work/gh-pages/$feed_path"

pub_date=$(date -u +"%a, %d %b %Y %H:%M:%S +0000")
sig_attr=""
if [[ -n "$ed_signature" && "$ed_signature" != "null" ]]; then
  sig_attr=" sparkle:edSignature=\"${ed_signature}\""
fi

item=$(cat <<EOF
    <item>
      <title>${title}</title>
      <pubDate>${pub_date}</pubDate>
      <sparkle:version>${build}</sparkle:version>
      <sparkle:shortVersionString>${marketing}</sparkle:shortVersionString>
      <enclosure url="${browser_url}" length="${length}" type="application/octet-stream"${sig_attr}/>
    </item>
EOF
)

if [[ ! -f "$feed_file" ]]; then
  cat > "$feed_file" <<EOF
<?xml version="1.0" encoding="utf-8"?>
<rss version="2.0" xmlns:sparkle="http://www.andymatuschak.org/xml-namespaces/sparkle" xmlns:dc="http://purl.org/dc/elements/1.1/">
  <channel>
    <title>${app} updates</title>
    <link>${pages_feed_url}</link>
    <description>Sparkle updates for ${app}</description>
    <language>en</language>
${item}
  </channel>
</rss>
EOF
else
  # Insert the new item after <language>…</language> (newest first).
  python3 - "$feed_file" "$item" <<'PY'
import sys
path, item = sys.argv[1], sys.argv[2]
text = open(path, encoding="utf-8").read()
needle = "</language>"
idx = text.find(needle)
if idx < 0:
    raise SystemExit("appcast missing </language>")
idx += len(needle)
text = text[:idx] + "\n" + item + text[idx:]
open(path, "w", encoding="utf-8").write(text)
PY
fi

git -C "$work/gh-pages" config user.name "github-actions[bot]"
git -C "$work/gh-pages" config user.email "41898282+github-actions[bot]@users.noreply.github.com"
git -C "$work/gh-pages" add "$feed_path"
if git -C "$work/gh-pages" diff --cached --quiet; then
  echo "Appcast unchanged."
else
  git -C "$work/gh-pages" commit -m "chore(macos): update ${app} Sparkle appcast to ${marketing}"
  git -C "$work/gh-pages" push origin gh-pages
fi

echo "Appcast: ${pages_feed_url}"
echo "Done."
