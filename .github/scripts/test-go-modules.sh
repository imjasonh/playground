#!/usr/bin/env bash
# Build and test the Go modules listed in MODULES as JSON.
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

mapfile -t modules < <(printf '%s' "${MODULES:-[]}" | jq -r '.[]')

if [ "${#modules[@]}" -eq 0 ]; then
  echo "No Go apps changed. Nothing to test."
  exit 0
fi

result=0
for module in "${modules[@]}"; do
  echo "::group::Build and test ${module}"

  if (
    cd "$module"
    go build ./...
  ); then
    echo "${module}: build passed"
  else
    echo "::error title=Go build failed::${module}: go build ./..."
    result=1
  fi

  # node-image layout conformance tests compare against pnpm; install it when needed.
  if [ "$module" = "node-image" ]; then
    if ! command -v pnpm >/dev/null 2>&1; then
      echo "Installing pnpm for node-image conformance tests"
      npm install -g pnpm@10
    fi
    if ! command -v node >/dev/null 2>&1; then
      echo "::warning title=node missing::node-image conformance tests that need node will skip"
    fi
  fi

  # kube end-to-end tests run a real kube-apiserver and etcd, and skip
  # without KUBEBUILDER_ASSETS, so download the binaries first.
  kube_assets=""
  if [ "$module" = "kube" ]; then
    if kube_assets=$(bash kube/fetch-envtest.sh); then
      echo "kube: running end-to-end tests with binaries from ${kube_assets}"
    else
      echo "::error title=kube envtest::kube/fetch-envtest.sh could not download kube-apiserver and etcd"
      result=1
    fi
  fi

  if (
    cd "$module"
    # -race is the Go equivalent of a data-race detector. Always on in CI.
    # -v so CI logs show each test (including Docker e2e PASS vs SKIP).
    # node-image Docker-socket e2e builds/runs several images; allow headroom.
    # pasta e2e shallow-clones real repos and cold-parses them; allow headroom.
    # The kind end-to-end tests of git-k8s, kube, and sshapp run in parallel
    # steps, in test-kind-e2e.sh.
    if [ "$module" = "node-image" ] || [ "$module" = "pasta" ]; then
      go test -race -v -timeout 30m ./...
    elif [ "$module" = "kube" ]; then
      # -count=1: the end-to-end tests run examples with go run, and the test
      # cache doesn't track the files that a subprocess reads.
      KUBEBUILDER_ASSETS="$kube_assets" go test -race -v -count=1 ./...
    else
      go test -race -v ./...
    fi
  ); then
    echo "${module}: tests passed"
  else
    echo "::error title=Go tests failed::${module}: go test -race -v ./..."
    result=1
  fi

  echo "::endgroup::"
done

exit "$result"
