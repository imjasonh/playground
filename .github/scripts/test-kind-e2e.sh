#!/usr/bin/env bash
# Run the kind end-to-end test of one Go module: git-k8s, kube, or sshapp.
# test.yml runs each as its own step, in parallel with the unit tests in
# test-go-modules.sh, because a kind test spends most of its time waiting for
# a cluster and its Pods. The tests' clusters, registries, and ports have
# different names, so they can run at the same time on one runner.
set -uo pipefail

module="${1:?usage: test-kind-e2e.sh MODULE}"

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
