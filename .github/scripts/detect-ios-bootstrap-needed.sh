#!/usr/bin/env bash
# Decide whether an iOS change set needs a signing re-bootstrap (new extension
# Bundle ID and/or App ID capability / entitlement that match must refresh).
#
# Mirrors the rules in ios/AGENTS.md ("Will my change need re-bootstrap?").
# Idempotent bootstrap is cheap relative to a failed TestFlight upload, but we
# still avoid flagging ordinary experiment / Info.plist / test-only edits.
#
# Usage:
#   detect-ios-bootstrap-needed.sh --from-changes [path...]
#     Paths via args, or stdin (one path per line) when no path args.
#
#   detect-ios-bootstrap-needed.sh --diff <git-rev-range>
#     Inspect the named range (e.g. origin/main...HEAD). Paths come from the
#     range; content-sensitive checks use the same range.
#
# Environment:
#   DIFF_RANGE   Optional git rev range used when inspecting project.yml /
#                Fastfile hunks under --from-changes. Required for those files
#                to be content-scanned; without it, Matchfile / *.entitlements
#                path hits still count, and any change to project.yml or
#                Fastfile is treated conservatively as needed.
#   GITHUB_OUTPUT  When set, also writes needed=true|false for Actions.
#
# Output: prints "true" or "false" to stdout. Always exits 0 on success.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

# Patterns in project.yml / Fastfile diffs that imply App ID / profile churn.
# Info.plist privacy strings and UIBackgroundModes are intentionally excluded.
PROJECT_YML_PATTERN='PRODUCT_BUNDLE_IDENTIFIER|CODE_SIGN_ENTITLEMENTS|[[:space:]]entitlements:|type:[[:space:]]*app-extension|com\.apple\.developer\.'
FASTFILE_PATTERN='SIGNING_IDENTIFIERS|ensure_bundle_ids!|ensure_healthkit!|APP_IDENTIFIER|KEYBOARD_IDENTIFIER|RIDE_WIDGET_IDENTIFIER|WATCH_IDENTIFIER|app_identifier:|BundleId|signing_bootstrap'

is_ios_signing_path() {
  local path="$1"
  local top="${path%%/*}"
  [[ -n "$top" && -f "$top/project.yml" ]] || return 1
  case "$path" in
    */fastlane/Matchfile) return 0 ;;
    *.entitlements) return 0 ;;
    */project.yml) return 0 ;;
    */fastlane/Fastfile) return 0 ;;
    *) return 1 ;;
  esac
}

path_always_needs_bootstrap() {
  local path="$1"
  case "$path" in
    */fastlane/Matchfile) return 0 ;;
    *.entitlements) return 0 ;;
    *) return 1 ;;
  esac
}

# True when the unified diff for $path under $range touches a signing-related
# line (added or removed). Empty / missing diffs → false.
diff_touches_pattern() {
  local range="$1"
  local path="$2"
  local pattern="$3"
  local hunk
  hunk=$(git diff -U0 "$range" -- "$path" 2>/dev/null || true)
  [[ -z "$hunk" ]] && return 1
  # Only added/removed lines, not headers (+++ / ---) or hunk marks.
  printf '%s\n' "$hunk" | grep -E '^[+-]' | grep -Ev '^[+-]{3} ' | grep -Eq "$pattern"
}

emit_needed() {
  local needed="$1"
  echo "$needed"
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    echo "needed=${needed}" >> "$GITHUB_OUTPUT"
  fi
}

evaluate_paths() {
  local range="$1"
  shift
  local path
  local any_signing_path=0

  for path in "$@"; do
    [[ -z "$path" ]] && continue
    is_ios_signing_path "$path" || continue
    any_signing_path=1

    if path_always_needs_bootstrap "$path"; then
      echo "bootstrap trigger: ${path} (Matchfile or entitlements)" >&2
      emit_needed true
      return 0
    fi

    case "$path" in
      */project.yml)
        if [[ -n "$range" ]]; then
          if diff_touches_pattern "$range" "$path" "$PROJECT_YML_PATTERN"; then
            echo "bootstrap trigger: ${path} (bundle id / entitlement / extension target)" >&2
            emit_needed true
            return 0
          fi
          echo "skip: ${path} changed but no signing-related hunks" >&2
        else
          echo "bootstrap trigger: ${path} (no DIFF_RANGE; treating project.yml change as needed)" >&2
          emit_needed true
          return 0
        fi
        ;;
      */fastlane/Fastfile)
        if [[ -n "$range" ]]; then
          if diff_touches_pattern "$range" "$path" "$FASTFILE_PATTERN"; then
            echo "bootstrap trigger: ${path} (signing identifiers / ensure_* / match)" >&2
            emit_needed true
            return 0
          fi
          echo "skip: ${path} changed but no signing-related hunks" >&2
        else
          echo "bootstrap trigger: ${path} (no DIFF_RANGE; treating Fastfile change as needed)" >&2
          emit_needed true
          return 0
        fi
        ;;
    esac
  done

  if ((any_signing_path == 0)); then
    echo "no iOS signing-related paths in change set" >&2
  fi
  emit_needed false
}

read_paths() {
  if (("$#" > 0)); then
    printf '%s\n' "$@"
  else
    cat
  fi
}

mode="${1:---from-changes}"

case "$mode" in
  --diff)
    range="${2:?Usage: $0 --diff <git-rev-range>}"
    paths=()
    while IFS= read -r path; do
      [[ -n "$path" ]] && paths+=("$path")
    done < <(git diff --name-only "$range")
    evaluate_paths "$range" "${paths[@]}"
    ;;
  --from-changes)
    shift
    paths=()
    while IFS= read -r path; do
      [[ -n "$path" ]] && paths+=("$path")
    done < <(read_paths "$@")
    evaluate_paths "${DIFF_RANGE:-}" "${paths[@]}"
    ;;
  *)
    echo "Usage: $0 --from-changes [path...] | --diff <git-rev-range>" >&2
    exit 1
    ;;
esac
