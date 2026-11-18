#!/usr/bin/env bash
# Run the kind end-to-end test of one Go module: git-k8s, kube, sshapp, or
# ci-substrate. test.yml runs each in its own job, beside the Go unit tests,
# because a kind test spends most of its time waiting for a cluster and its
# Pods.
#
# Usage:
#   test-kind-e2e.sh MODULE
#   test-kind-e2e.sh --list    print the modules that have a kind test, as JSON
set -uo pipefail

kind_modules=(git-k8s kube sshapp ci-substrate)

module="${1:?usage: test-kind-e2e.sh MODULE | --list}"
if [ "$module" = "--list" ]; then
  printf '%s\n' "${kind_modules[@]}" | jq -R . | jq -cs .
  exit 0
fi

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root/$module" || exit 1

if ! command -v docker >/dev/null 2>&1; then
  echo "::error title=${module} kind e2e::docker is required"
  exit 1
fi
if ! docker info >/dev/null 2>&1; then
  echo "::error title=${module} kind e2e::docker daemon is not reachable"
  exit 1
fi

case "$module" in
  git-k8s)
    # Installs the controllers and checks with kube's generate command, and
    # pushes branches to a git server that runs on the runner. Needs git.
    GIT_K8S_KIND_E2E=1 go test -v -count=1 -timeout 20m ./e2e/kind/
    ;;
  kube)
    # Installs the examples with generate, which pushes their images to a
    # local registry.
    KUBE_KIND_E2E=1 go test -v -count=1 -timeout 20m ./e2e/kind/
    ;;
  sshapp)
    # The mux and hello apps: scale-up, the registry menu, and scale-to-zero.
    SSHAPP_KIND_E2E=1 go test -race -v -timeout 20m ./e2e/
    ;;
  ci-substrate)
    # Multi-tenant CAS + node-local verified cache, deployed with ko apply.
    # It also builds with Bazel and dogfoods ci-substrate on the cluster,
    # which took over 20 minutes when it shared a runner with the other tests.
    CI_SUBSTRATE_KIND_E2E=1 go test -race -v -timeout 40m ./e2e/
    ;;
  *)
    echo "::error title=kind e2e::${module} has no kind end-to-end test"
    exit 1
    ;;
esac
status=$?
if [ "$status" -ne 0 ]; then
  echo "::error title=${module} kind e2e failed::${module}: its kind end-to-end test failed"
  exit "$status"
fi
echo "${module}: kind e2e passed"
