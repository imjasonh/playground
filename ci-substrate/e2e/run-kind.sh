#!/usr/bin/env bash
# Spin up a KinD cluster, ko-apply the cas + cascache control plane, and run
# cictl against them over port-forwards to prove multi-tenant isolation and
# node-local cache reuse. Invoked by go test ./e2e when CI_SUBSTRATE_KIND_E2E=1.
#
# Builds and deploys go through ko only: there are no Dockerfiles and no Helm
# charts. Images land in the kind local registry at KO_DOCKER_REPO.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLUSTER_NAME="${CI_SUBSTRATE_KIND_CLUSTER:-ci-substrate-e2e}"
WORKDIR="${TMPDIR:-/tmp}/ci-substrate-kind-e2e-$$"
KIND_CREATED=0
REGISTRY_NAME="${CI_SUBSTRATE_REGISTRY_NAME:-ci-substrate-registry}"
# 5312 avoids the git-k8s kind e2e registry default (5002) when several kind
# legs run in parallel on one runner.
REGISTRY_PORT="${CI_SUBSTRATE_REGISTRY_PORT:-5312}"
PORT_FORWARD_PIDS=()

cleanup() {
  local pid
  for pid in "${PORT_FORWARD_PIDS[@]:-}"; do
    if [[ -n "${pid}" ]] && kill -0 "${pid}" 2>/dev/null; then
      kill "${pid}" 2>/dev/null || true
      wait "${pid}" 2>/dev/null || true
    fi
  done
  if [[ "${CI_SUBSTRATE_KIND_KEEP:-}" != "1" && "${KIND_CREATED}" -eq 1 ]]; then
    kind delete cluster --name "${CLUSTER_NAME}" >/dev/null 2>&1 || true
  fi
  if [[ "${CI_SUBSTRATE_KIND_KEEP:-}" != "1" ]]; then
    docker rm -f "${REGISTRY_NAME}" >/dev/null 2>&1 || true
  fi
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

install_kind() {
  if command -v kind >/dev/null 2>&1; then
    return
  fi
  local ver="${KIND_VERSION:-v0.27.0}"
  local os arch url
  os="$(uname -s | tr '[:upper:]' '[:lower:]')"
  arch="$(uname -m)"
  case "${arch}" in
    x86_64) arch=amd64 ;;
    aarch64 | arm64) arch=arm64 ;;
  esac
  url="https://kind.sigs.k8s.io/dl/${ver}/kind-${os}-${arch}"
  echo "Installing kind ${ver}"
  curl -fsSL -o "${WORKDIR}/kind" "${url}"
  chmod +x "${WORKDIR}/kind"
  export PATH="${WORKDIR}:${PATH}"
}

install_ko() {
  if command -v ko >/dev/null 2>&1; then
    return
  fi
  echo "Installing ko"
  GOBIN="${WORKDIR}" go install github.com/google/ko@v0.17.1
  export PATH="${WORKDIR}:${PATH}"
}

install_kubectl() {
  if command -v kubectl >/dev/null 2>&1; then
    return
  fi
  local ver os arch
  ver="$(curl -fsSL https://dl.k8s.io/release/stable.txt)"
  os="$(uname -s | tr '[:upper:]' '[:lower:]')"
  arch="$(uname -m)"
  case "${arch}" in
    x86_64) arch=amd64 ;;
    aarch64 | arm64) arch=arm64 ;;
  esac
  echo "Installing kubectl ${ver}"
  curl -fsSL -o "${WORKDIR}/kubectl" "https://dl.k8s.io/release/${ver}/bin/${os}/${arch}/kubectl"
  chmod +x "${WORKDIR}/kubectl"
  export PATH="${WORKDIR}:${PATH}"
}

ensure_registry() {
  if docker inspect -f '{{.State.Running}}' "${REGISTRY_NAME}" 2>/dev/null | grep -q true; then
    return
  fi
  docker rm -f "${REGISTRY_NAME}" >/dev/null 2>&1 || true
  docker run -d --restart=always \
    -p "127.0.0.1:${REGISTRY_PORT}:5000" \
    --name "${REGISTRY_NAME}" \
    registry:2 >/dev/null
}

create_cluster() {
  if kind get clusters 2>/dev/null | grep -qx "${CLUSTER_NAME}"; then
    echo "Reusing kind cluster ${CLUSTER_NAME}"
    return
  fi
  cat >"${WORKDIR}/kind.yaml" <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
containerdConfigPatches:
- |-
  [plugins."io.containerd.grpc.v1.cri".registry]
    config_path = "/etc/containerd/certs.d"
nodes:
- role: control-plane
EOF
  kind create cluster --name "${CLUSTER_NAME}" --config "${WORKDIR}/kind.yaml"
  KIND_CREATED=1

  # Point the node at the host's local registry.
  docker network connect kind "${REGISTRY_NAME}" 2>/dev/null || true
  local reg_dir="/etc/containerd/certs.d/localhost:${REGISTRY_PORT}"
  for node in $(kind get nodes --name "${CLUSTER_NAME}"); do
    docker exec "${node}" mkdir -p "${reg_dir}"
    docker exec -i "${node}" tee "${reg_dir}/hosts.toml" >/dev/null <<EOF
[host."http://${REGISTRY_NAME}:5000"]
  capabilities = ["pull", "resolve"]
EOF
  done
}

await_ready() {
  local kind=$1 name=$2
  kubectl -n ci-substrate wait --for=condition=Available --timeout=180s "${kind}/${name}"
}

mkdir -p "${WORKDIR}"
need_cmd docker
need_cmd go
need_cmd curl
install_kind
install_ko
install_kubectl
need_cmd kind
need_cmd ko
need_cmd kubectl

ensure_registry
create_cluster
kubectl cluster-info --context "kind-${CLUSTER_NAME}" >/dev/null

export KO_DOCKER_REPO="localhost:${REGISTRY_PORT}/ci-substrate"
# Prefer the repo's chainguard static base; when that registry is unreachable
# (egress-restricted VMs), fall back to the docker.io mirror of the same image.
if [[ -z "${KO_DEFAULTBASEIMAGE:-}" ]]; then
  if ! curl -fsS --max-time 3 https://cgr.dev/v2/ >/dev/null 2>&1; then
    export KO_DEFAULTBASEIMAGE=registry-1.docker.io/chainguard/static:latest
    echo "cgr.dev unreachable; using ${KO_DEFAULTBASEIMAGE}"
  fi
fi

cd "${ROOT}"
echo "ko apply deploy/"
# Apply the static config first (no images), then the image-bearing resources
# so a ko resolve failure does not leave a half-applied namespace alone.
kubectl apply -f deploy/00-namespace-and-config.yaml
ko apply -f deploy/10-cas.yaml
await_ready deployment cas

# cascache must reach cas without relying on ClusterIP/DNS inside the
# hostNetwork pod. Point ORIGIN_ADDR at the cas Pod IP once, then roll out
# cascache a single time so we do not replace the pod under a port-forward.
CAS_POD_IP="$(kubectl -n ci-substrate get pod -l app=cas -o jsonpath='{.items[0].status.podIP}')"
echo "Using cas pod IP ${CAS_POD_IP}:8980"
ko resolve -f deploy/20-cascache.yaml \
  | sed "s#cas.ci-substrate.svc.cluster.local#${CAS_POD_IP}#g" \
  | kubectl apply -f -
kubectl -n ci-substrate rollout status daemonset/cascache --timeout=300s

# Port-forward Services (stable targets) from the host. This avoids pinning a
# DaemonSet pod name that a second rollout would replace, which broke CI.
LOCAL_ORIGIN_PORT=18980
LOCAL_CACHE_PORT=19092
LOCAL_METRICS_PORT=19090
kubectl -n ci-substrate port-forward svc/cas "${LOCAL_ORIGIN_PORT}:8980" >/dev/null &
PORT_FORWARD_PIDS+=($!)
kubectl -n ci-substrate port-forward svc/cascache "${LOCAL_CACHE_PORT}:9092" "${LOCAL_METRICS_PORT}:9090" >/dev/null &
PORT_FORWARD_PIDS+=($!)

await_tcp_port() {
  local port=$1
  local deadline=$((SECONDS + 60))
  while ((SECONDS < deadline)); do
    if (echo >/dev/tcp/127.0.0.1/"${port}") >/dev/null 2>&1; then
      return 0
    fi
    sleep 0.5
  done
  echo "timed out waiting for 127.0.0.1:${port}" >&2
  return 1
}

for port in "${LOCAL_ORIGIN_PORT}" "${LOCAL_CACHE_PORT}" "${LOCAL_METRICS_PORT}"; do
  await_tcp_port "${port}"
done

echo "Running cictl demo against port-forwards"
go build -o "${WORKDIR}/cictl" ./cmd/cictl
"${WORKDIR}/cictl" \
  -origin-addr="127.0.0.1:${LOCAL_ORIGIN_PORT}" \
  -cache-addr="127.0.0.1:${LOCAL_CACHE_PORT}" \
  -cache-metrics-url="http://127.0.0.1:${LOCAL_METRICS_PORT}" \
  -token-a=tok-a \
  -token-b=tok-b \
  -instance-a=tenant-a \
  -shared=shared

echo "ci-substrate kind e2e passed"
