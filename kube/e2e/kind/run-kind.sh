#!/usr/bin/env bash
# Install the website and podpolicy examples in a kind cluster with
# generate, which pushes their images to a local registry, and check that
# they work. go test ./e2e/kind runs this when KUBE_KIND_E2E=1, which CI
# sets when kube changes.
#
# KUBE_KIND_CHAINGUARD is where Chainguard's images come from
# (cgr.dev/chainguard; docker.io/chainguard is a mirror).
# KUBE_KIND_KEEP=1 keeps the cluster and registry afterward.
set -euo pipefail

KUBE="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CLUSTER="${KUBE_KIND_CLUSTER:-kube-e2e}"
CONTEXT="kind-${CLUSTER}"
REGISTRY="${KUBE_KIND_REGISTRY:-kube-e2e-registry}"
PORT="${KUBE_KIND_REGISTRY_PORT:-5001}"
CHAINGUARD="${KUBE_KIND_CHAINGUARD:-cgr.dev/chainguard}"
PLATFORM="linux/$(go env GOARCH)"
WORKDIR="$(mktemp -d)"
CREATED_CLUSTER=0
CREATED_REGISTRY=0
PORT_FORWARD_PID=""

k() { kubectl --context "${CONTEXT}" "$@"; }

diagnose() {
  echo "::group::Cluster state"
  k get nodes,websites,all -A -o wide || true
  for ns in website podpolicy; do
    k -n "${ns}" describe pods || true
    k -n "${ns}" logs --all-containers --prefix --tail=200 -l "app.kubernetes.io/name=${ns}" || true
  done
  echo "::endgroup::"
}

finish() {
  local status=$?
  if [[ -n "${PORT_FORWARD_PID}" ]]; then
    kill "${PORT_FORWARD_PID}" 2>/dev/null || true
  fi
  if [[ ${status} -ne 0 ]]; then
    diagnose
  fi
  if [[ "${KUBE_KIND_KEEP:-}" != 1 ]]; then
    if [[ ${CREATED_CLUSTER} -eq 1 ]]; then
      kind delete cluster --name "${CLUSTER}" || true
    fi
    if [[ ${CREATED_REGISTRY} -eq 1 ]]; then
      docker rm -f "${REGISTRY}" >/dev/null || true
    fi
  fi
  rm -rf "${WORKDIR}"
  exit "${status}"
}
trap finish EXIT

# eventually runs a command until it succeeds, for up to $1 seconds.
eventually() {
  local timeout=$1
  shift
  local deadline=$((SECONDS + timeout))
  until "$@"; do
    if ((SECONDS >= deadline)); then
      echo "timed out after ${timeout}s: $*" >&2
      return 1
    fi
    sleep 2
  done
}

need() {
  command -v "$1" >/dev/null || {
    echo "$1 is required" >&2
    exit 1
  }
}

install_kind() {
  if command -v kind >/dev/null; then
    return
  fi
  local arch
  arch="$(go env GOARCH)"
  echo "Installing kind ${KIND_VERSION:-v0.33.0}"
  curl -fsSL -o "${WORKDIR}/kind" "https://kind.sigs.k8s.io/dl/${KIND_VERSION:-v0.33.0}/kind-linux-${arch}"
  chmod +x "${WORKDIR}/kind"
  export PATH="${WORKDIR}:${PATH}"
}

need docker
need kubectl
need go
need curl
install_kind
docker info >/dev/null

echo "::group::Start a registry and a kind cluster"
# As in https://kind.sigs.k8s.io/docs/user/local-registry/: nodes pull
# localhost:PORT/... from the registry container, which is on kind's
# network.
if [[ "$(docker inspect -f '{{.State.Running}}' "${REGISTRY}" 2>/dev/null || true)" != true ]]; then
  docker run -d --restart=always -p "127.0.0.1:${PORT}:5000" --name "${REGISTRY}" registry:2
  CREATED_REGISTRY=1
fi
if ! kind get clusters 2>/dev/null | grep -x "${CLUSTER}" >/dev/null; then
  # kube-proxy's nftables mode works on kernels without the iptables
  # statistic match, which iptables mode needs for Services with more than
  # one endpoint.
  kind create cluster --name "${CLUSTER}" --wait 120s --config - <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
networking:
  kubeProxyMode: nftables
EOF
  CREATED_CLUSTER=1
fi
for node in $(kind get nodes --name "${CLUSTER}"); do
  docker exec "${node}" mkdir -p "/etc/containerd/certs.d/localhost:${PORT}"
  printf '[host."http://%s:5000"]\n' "${REGISTRY}" |
    docker exec -i "${node}" cp /dev/stdin "/etc/containerd/certs.d/localhost:${PORT}/hosts.toml"
done
if [[ "$(docker inspect -f '{{json .NetworkSettings.Networks.kind}}' "${REGISTRY}")" == null ]]; then
  docker network connect kind "${REGISTRY}"
fi
k version
echo "::endgroup::"

cd "${KUBE}"
generate() {
  local example=$1
  shift
  go run "./examples/${example}" generate -registry="localhost:${PORT}/kube-e2e" \
    -base="${CHAINGUARD}/static:latest" -platform="${PLATFORM}" "$@"
}

echo "::group::Install the website example"
generate website | k apply -f -
k -n website rollout status deployment/website --timeout=180s

website_ready() {
  [[ "$(k get website hello -o jsonpath='{.status.readyReplicas}')" == "$1" ]]
}
k apply -f - <<EOF
apiVersion: examples.kube.imjasonh.github.io/v1
kind: Website
metadata:
  name: hello
  namespace: default
spec:
  image: ${CHAINGUARD}/nginx:latest
  replicas: 2
  port: 8080
EOF
eventually 180 website_ready 2
k get website hello
[[ "$(k get deployment hello -o jsonpath='{.metadata.ownerReferences[0].kind}')" == Website ]]
[[ "$(k get website hello -o jsonpath='{.status.url}')" == http://hello.default.svc ]]

k port-forward service/hello 18080:80 >"${WORKDIR}/port-forward.log" 2>&1 &
PORT_FORWARD_PID=$!
eventually 30 curl -fsS -o /dev/null http://127.0.0.1:18080/
kill "${PORT_FORWARD_PID}"
PORT_FORWARD_PID=""
echo "The Service serves the site."

# Every replica of the controller goes away; the new ones take over.
k -n website delete pods -l app.kubernetes.io/name=website
k -n website rollout status deployment/website --timeout=180s
k patch website hello --type=merge -p '{"spec":{"replicas":3}}'
eventually 180 website_ready 3
echo "The controller's new pods reconcile."

k delete website hello
deployment_gone() { ! k get deployment hello >/dev/null 2>&1; }
eventually 120 deployment_gone
echo "Deleting the Website deletes what it owned."
echo "::endgroup::"

echo "::group::Install the podpolicy example"
generate podpolicy | k apply -f -
k -n podpolicy rollout status deployment/podpolicy --timeout=180s
k create namespace policy-e2e

# The webhooks are registered by the program when it starts, so wait for
# the denial rather than an error from calling a webhook that isn't ready.
denied() {
  local out
  if out="$(k -n policy-e2e run denied --image="${CHAINGUARD}/nginx:latest" --restart=Never --dry-run=server -o name 2>&1)"; then
    echo "allowed: ${out}" >&2
    return 1
  fi
  echo "${out}"
  [[ "${out}" == *"isn't from an allowed registry"* ]]
}
eventually 120 denied

requests="$(k -n policy-e2e run allowed --image=registry.example.com/app:1 --restart=Never --dry-run=server \
  -o jsonpath='{.spec.containers[0].resources.requests}')"
echo "defaulted requests: ${requests}"
[[ "${requests}" == *'"cpu":"100m"'* && "${requests}" == *'"memory":"128Mi"'* ]]

k -n kube-system run exempt --image="${CHAINGUARD}/nginx:latest" --restart=Never --dry-run=server -o name
echo "::endgroup::"

echo "kind e2e passed"
