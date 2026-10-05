#!/usr/bin/env bash
# Install the website, imagereport, janitor, and podpolicy examples in a kind
# cluster with generate, which pushes their images to a local registry, and
# check that they work. go test ./e2e/kind runs this when KUBE_KIND_E2E=1,
# which CI sets when kube changes.
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
  for ns in website imagereport janitor podpolicy; do
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

serving_event() {
  k describe website hello | grep -E "Normal +Serving .+ website +$1 of $1 replicas are ready"
}
eventually 60 serving_event 2
k describe website hello | sed -n '/^Events:/,$p'
echo "kubectl describe shows the Website's events."

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
eventually 60 serving_event 3
echo "The controller's new pods reconcile and record events."

k delete website hello
deployment_gone() { ! k get deployment hello >/dev/null 2>&1; }
eventually 120 deployment_gone
echo "Deleting the Website deletes what it owned."
echo "::endgroup::"

# podpolicy's webhooks deny Pods from this registry, so imagereport and
# janitor go first.
echo "::group::Install the imagereport example"
generate imagereport -replicas=1 | k apply -f -
k -n imagereport rollout status deployment/imagereport --timeout=180s

# The program owns ImageReports without reconciling them, so it creates their
# CRD with the rules that generate wrote.
crd_created() {
  [[ "$(k get crd imagereports.examples.kube.imjasonh.github.io \
    -o jsonpath='{.metadata.labels.kube\.imjasonh\.github\.io/managed-by}')" == imagereport ]]
}
eventually 60 crd_created
has_report() {
  [[ "$(k -n "$1" get imagereport images -o jsonpath='{.images[*].image}' 2>/dev/null)" == *"$2"* ]]
}
eventually 60 has_report imagereport "/kube-e2e/imagereport@sha256:"
eventually 60 has_report kube-system kube-apiserver
k get imagereports -A
echo "The program created the ImageReport CRD and reports pods' images."
echo "::endgroup::"

echo "::group::Install the janitor example"
generate janitor | k apply -f -
k -n janitor rollout status deployment/janitor --timeout=180s
# janitor has no Finalize method and owns nothing, so generate doesn't let it
# patch namespaces.
[[ "$(k auth can-i patch namespaces --as=system:serviceaccount:janitor:janitor)" == no ]]
namespace_gone() { ! k get namespace "$1" >/dev/null 2>&1; }
namespace_deleting() { [[ -n "$(k get namespace "$1" -o jsonpath='{.metadata.deletionTimestamp}')" ]]; }
k apply -f - <<EOF
apiVersion: v1
kind: Namespace
metadata:
  name: janitor-e2e
  annotations:
    janitor.examples.kube.imjasonh.github.io/ttl: 1s
EOF
eventually 120 namespace_gone janitor-e2e
echo "janitor deletes an expired namespace without permission to patch it."

# A finalizer that an earlier version of janitor added stays, because
# removing it takes patch, and janitor's error names the option to add.
k apply -f - <<EOF
apiVersion: v1
kind: Namespace
metadata:
  name: janitor-stale
  annotations:
    janitor.examples.kube.imjasonh.github.io/ttl: 1s
  finalizers:
  - kube.imjasonh.github.io/janitor
EOF
names_option() {
  [[ "$(k -n janitor logs -l app.kubernetes.io/name=janitor --tail=-1)" == *'pass kube.RemovesFinalizer() to kube.For'* ]]
}
eventually 120 namespace_deleting janitor-stale
eventually 120 names_option
[[ "$(k get namespace janitor-stale -o jsonpath='{.metadata.finalizers}')" == *kube.imjasonh.github.io/janitor* ]]
k patch namespace janitor-stale --type=json -p '[{"op":"remove","path":"/metadata/finalizers"}]'
eventually 120 namespace_gone janitor-stale
echo "janitor can't remove a finalizer that an earlier version added, and its error names kube.RemovesFinalizer."
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
