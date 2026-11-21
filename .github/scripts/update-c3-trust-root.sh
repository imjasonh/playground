#!/usr/bin/env bash
# Keeps c3-boot's pinned Sigstore files current for the c3-trust-root
# workflow, and opens, updates, or closes its pull request.
#
#   update-c3-trust-root.sh fetch
#     Copies Sigstore's production trusted root and Rekor v2 signing
#     configuration from sigstore/root-signing into c3-boot/release/, drops
#     every log except Rekor v2 logs from the signing configuration, and
#     records the source commit in c3-boot/release/README.md. Commits any
#     change on a fresh automation branch. Writes the outputs result
#     (unchanged, changed, or skipped when someone else pushed to the
#     branch), remote, and commit.
#   update-c3-trust-root.sh open-pr
#     Pushes the branch and opens or updates its pull request. Reads COMMIT,
#     REMOTE (the branch's commit when fetch ran, or empty), and DESCRIPTION,
#     a file with the c3-ota describe output, from the environment.
#   update-c3-trust-root.sh close-stale
#
# C3_ROOT_SIGNING_DIR, when set, names a local directory with
# trusted_root.json and signing_config_rekor_v2.v0.2.json to use instead of
# the GitHub API, with C3_ROOT_SIGNING_COMMIT as their commit. Tests set it.
set -euo pipefail

BRANCH="${C3_TRUST_ROOT_BRANCH:-automation/c3-trust-root}"
BASE="${C3_TRUST_ROOT_BASE:-main}"
RELEASE="${C3_RELEASE_DIR:-c3-boot/release}"
SOURCE_REPO="sigstore/root-signing"
BOT_NAME="github-actions[bot]"
BOT_EMAIL="41898282+github-actions[bot]@users.noreply.github.com"

_output() {
  echo "$1=$2" >> "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
}

_configure_auth() {
  if [[ -n "${GH_TOKEN:-}" && -n "${GITHUB_REPOSITORY:-}" ]]; then
    git remote set-url origin "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
  fi
}

# _download COMMIT NAME OUT copies targets/NAME at COMMIT to OUT.
_download() {
  if [[ -n "${C3_ROOT_SIGNING_DIR:-}" ]]; then
    cp "${C3_ROOT_SIGNING_DIR}/$2" "$3"
  else
    gh api -H "Accept: application/vnd.github.raw" \
      "repos/${SOURCE_REPO}/contents/targets/$2?ref=$1" >"$3"
  fi
}

# _rekor_v2_only IN OUT writes IN's signing configuration with only its
# Rekor v2 logs. c3-boot accepts only Rekor v2 entries, and with more than
# one log listed, cosign may pick any of them.
_rekor_v2_only() {
  python3 - "$1" "$2" <<'EOF'
import json
import sys

src, dst = sys.argv[1], sys.argv[2]
with open(src) as f:
    config = json.load(f)
logs = [l for l in config.get("rekorTlogUrls", []) if l.get("majorApiVersion") == 2]
if not logs:
    sys.exit("the signing configuration lists no Rekor v2 log")
config["rekorTlogUrls"] = logs
with open(dst, "w") as f:
    f.write(json.dumps(config, indent=2) + "\n")
EOF
}

case "${1:-}" in
  fetch)
    # Don't overwrite a branch that someone else pushed to, for example to
    # add a trust-root blob they signed.
    _configure_auth
    remote=""
    if git fetch --quiet origin "refs/heads/${BRANCH}:refs/remotes/origin/${BRANCH}" 2>/dev/null; then
      remote=$(git rev-parse "refs/remotes/origin/${BRANCH}")
      author=$(git log -1 --format=%ae "${remote}")
      if [[ "${author}" != "${BOT_EMAIL}" ]]; then
        echo "::notice::${BRANCH} has a commit by ${author}; leaving it alone."
        _output result skipped
        exit 0
      fi
    fi
    _output remote "${remote}"

    if [[ -n "${C3_ROOT_SIGNING_DIR:-}" ]]; then
      commit="${C3_ROOT_SIGNING_COMMIT:?C3_ROOT_SIGNING_COMMIT must be set}"
    else
      commit=$(gh api "repos/${SOURCE_REPO}/commits/main" --jq .sha)
    fi
    tmp=$(mktemp -d)
    trap 'rm -rf "${tmp}"' EXIT
    _download "${commit}" trusted_root.json "${tmp}/trusted_root.json"
    _download "${commit}" signing_config_rekor_v2.v0.2.json "${tmp}/signing_config.json"
    python3 -c 'import json, sys; json.load(open(sys.argv[1]))' "${tmp}/trusted_root.json"

    if cmp -s "${tmp}/trusted_root.json" "${RELEASE}/trusted_root.json" &&
      _rekor_v2_only "${tmp}/signing_config.json" "${tmp}/filtered.json" &&
      cmp -s "${tmp}/filtered.json" "${RELEASE}/signing_config.json"; then
      _output result unchanged
      exit 0
    fi

    git checkout -B "${BRANCH}"
    cp "${tmp}/trusted_root.json" "${RELEASE}/trusted_root.json"
    _rekor_v2_only "${tmp}/signing_config.json" "${RELEASE}/signing_config.json"
    sum=$(sha256sum "${RELEASE}/trusted_root.json" | cut -d' ' -f1)
    python3 - "${RELEASE}/README.md" "${commit}" "${sum}" <<'EOF'
import re
import sys

path, commit, digest = sys.argv[1:]
with open(path) as f:
    text = f.read()
text, n = re.subn(r"commit `[0-9a-f]{40}`", f"commit `{commit}`", text)
text, m = re.subn(r"SHA-256\n  `[0-9a-f]{64}`", f"SHA-256\n  `{digest}`", text)
if n != 1 or m != 1:
    sys.exit("README.md no longer has one commit and one SHA-256 to update")
with open(path, "w") as f:
    f.write(text)
EOF
    git config user.name "${BOT_NAME}"
    git config user.email "${BOT_EMAIL}"
    git add "${RELEASE}"
    git commit -q -m "c3-boot: update the pinned Sigstore trusted root

From ${SOURCE_REPO}@${commit}."
    _output result changed
    _output commit "${commit}"
    ;;

  open-pr)
    : "${COMMIT:?COMMIT must be set}" "${DESCRIPTION:?DESCRIPTION must be set}"
    _configure_auth
    # The lease fails the push if anyone pushed after fetch checked the
    # branch. An empty REMOTE means the branch must still not exist.
    git push --force-with-lease="refs/heads/${BRANCH}:${REMOTE:-}" origin "HEAD:refs/heads/${BRANCH}"
    title="c3-boot: update the pinned Sigstore trusted root"
    body="Sigstore's production trusted root or signing configuration changed in
[\`${SOURCE_REPO}@${COMMIT:0:12}\`](https://github.com/${SOURCE_REPO}/tree/${COMMIT}/targets).
This updates the copies in \`${RELEASE}/\` that \`c3-release.yml\` signs and
checks with.

Devices don't trust the new root until the current key set signs a
trust-root blob for it offline. Review these entries, which a blob built
from this root with \`c3-ota blob\` would hold, before signing one:

$(cat "${DESCRIPTION}")"
    existing=$(gh pr list --head "${BRANCH}" --base "${BASE}" --state open --json number --jq '.[0].number // empty')
    if [[ -n "${existing}" ]]; then
      gh pr edit "${existing}" --title "${title}" --body "${body}"
    else
      gh pr create --base "${BASE}" --head "${BRANCH}" --title "${title}" --body "${body}"
    fi
    ;;

  close-stale)
    existing=$(gh pr list --head "${BRANCH}" --base "${BASE}" --state open --json number --jq '.[0].number // empty')
    if [[ -n "${existing}" ]]; then
      gh pr close "${existing}" --delete-branch \
        --comment "The pinned files already match ${SOURCE_REPO}; closing." || true
    fi
    ;;

  *)
    echo "usage: $0 fetch | open-pr | close-stale" >&2
    exit 2
    ;;
esac
