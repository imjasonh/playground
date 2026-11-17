#!/usr/bin/env bash
# Update, build, and test every top-level Go module.
#
# Writes a "result" step output for the dependency workflow.
set -uo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${GITHUB_STEP_SUMMARY:?GITHUB_STEP_SUMMARY must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

result=success
{
  echo "### Daily Go dependency update"
  echo
} >> "$GITHUB_STEP_SUMMARY"

modules=()
if modules_json=$(bash .github/scripts/discover-go-modules.sh --all); then
  if module_lines=$(printf '%s' "$modules_json" | jq -r '.[]'); then
    if [ -n "$module_lines" ]; then
      mapfile -t modules <<< "$module_lines"
    fi
  else
    result=failure
    echo "::error title=Go app discovery failed::Discovery returned invalid JSON."
    echo "- ❌ Go app discovery returned invalid JSON." >> "$GITHUB_STEP_SUMMARY"
  fi
else
  result=failure
  echo "::error title=Go app discovery failed::Could not discover Go app modules."
  echo "- ❌ Could not discover Go app modules." >> "$GITHUB_STEP_SUMMARY"
fi

if [ "${#modules[@]}" -eq 0 ]; then
  echo "No Go apps found."
  if [ "$result" = success ]; then
    echo "- No Go apps found." >> "$GITHUB_STEP_SUMMARY"
  fi
fi

# Each module's go line follows the minor release this update runs with, so
# every module gets that release's language changes and GODEBUG defaults.
# The repository root has no go.mod, so this is the installed release.
go_line=$(go env GOVERSION | sed -E 's/^go([0-9]+\.[0-9]+).*/\1.0/')

for module in "${modules[@]}"; do
  if [ "$module" = "litestream" ]; then
    # The fork keeps upstream's dependency versions, so a later pull from
    # upstream merges cleanly. update-litestream.yml updates it instead.
    echo "- \`litestream\`: skipped; update-litestream.yml pulls upstream" >> "$GITHUB_STEP_SUMMARY"
    continue
  fi

  echo "::group::Update and verify ${module}"

  # Match test-go-modules.sh: cloudrun-sqlite builds the fork's VFS, which
  # needs the vfs tag, so go get also sees the VFS's dependencies.
  goflags="${GOFLAGS:-}"
  if [ "$module" = "cloudrun-sqlite" ]; then
    goflags="${goflags:+$goflags }-tags=vfs"
  fi

  current=$(cd "$module" && go mod edit -json | jq -r .Go)
  if [ "$(printf '%s\n%s\n' "$current" "$go_line" | sort -V | tail -n 1)" != "$current" ]; then
    if (cd "$module" && go mod edit -go="$go_line"); then
      echo "- ✅ \`${module}\`: go ${current} → ${go_line}" >> "$GITHUB_STEP_SUMMARY"
    else
      result=failure
      echo "::error title=Go version update failed::${module}: go mod edit -go=${go_line}"
      echo "- ❌ \`${module}\`: go version update failed" >> "$GITHUB_STEP_SUMMARY"
    fi
  fi

  # A module with scripts/update-deps.sh updates its own dependencies.
  update="go get -u ./..."
  if [ -f "$module/scripts/update-deps.sh" ]; then
    update="bash scripts/update-deps.sh"
  fi
  if (
    cd "$module"
    export GOFLAGS="$goflags"
    $update
  ); then
    echo "- ✅ \`${module}\`: dependencies updated" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Dependency update failed::${module}: ${update}"
    echo "- ❌ \`${module}\`: dependency update failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  # Same gate as test-go-modules.sh: an unformatted tree fails the update.
  if bash "${repo_root}/.github/scripts/check-gofmt.sh" "$module"; then
    echo "- ✅ \`${module}\`: gofmt ok" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=gofmt failed::${module}: gofmt would reformat a .go file outside vendor and testdata"
    echo "- ❌ \`${module}\`: gofmt failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    cd "$module"
    export GOFLAGS="$goflags"
    go build ./...
  ); then
    echo "- ✅ \`${module}\`: build passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Build failed::${module}: go build ./..."
    echo "- ❌ \`${module}\`: build failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  # Match test-go-modules.sh: node-image compile e2e needs pnpm on PATH in CI.
  if [ "$module" = "node-image" ]; then
    if ! command -v pnpm >/dev/null 2>&1; then
      echo "Installing pnpm for node-image conformance tests"
      npm install -g pnpm@10
    fi
  fi

  if (
    cd "$module"
    export GOFLAGS="$goflags"
    # Match test-go-modules.sh: always race-detect. Heavy modules get more time.
    if [ "$module" = "pasta" ]; then
      go test -race -timeout 30m ./... && CGO_ENABLED=0 go test ./internal/treesitter/
    elif [ "$module" = "node-image" ]; then
      go test -race -timeout 30m ./...
    else
      go test -race ./...
    fi
  ); then
    echo "- ✅ \`${module}\`: tests passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Tests failed::${module}: go test -race ./..."
    echo "- ❌ \`${module}\`: tests failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  echo "::endgroup::"
done

echo "result=${result}" >> "$GITHUB_OUTPUT"
