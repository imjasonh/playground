#!/usr/bin/env bash
# Spin up a KinD cluster, ko-apply the cas, cascache, and runner control
# plane, and run cictl against them over port-forwards to prove multi-tenant
# isolation, node-local cache reuse, and remote execution. Then build with
# stock Bazel as two users in two tenants (run-bazel.sh) to prove neither can
# see or change the other's results. Last, build and test ci-substrate itself
# with Bazel on the cluster (run-dogfood.sh; set CI_SUBSTRATE_DOGFOOD=0 to
# skip). Between the two, it checks that a Bazel build's trace reaches
# Jaeger and its metrics reach the collector (run-telemetry.sh). Invoked by
# go test ./e2e when CI_SUBSTRATE_KIND_E2E=1.
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
  local ver="${KUBECTL_VERSION:-v1.32.2}"
  local os arch
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

install_crane() {
  if command -v crane >/dev/null 2>&1; then
    return
  fi
  echo "Installing crane"
  GOBIN="${WORKDIR}" go install github.com/google/go-containerregistry/cmd/crane@v0.22.1
  export PATH="${WORKDIR}:${PATH}"
}

# mirror_images copies each third-party image a manifest names into the local
# registry, keeping its digest, and prints the manifest with the copies'
# references. Nodes then pull from the registry beside them, which also works
# where they cannot reach Docker Hub or ghcr.io, and avoids Docker Hub's pull
# limits. A Docker Hub image is copied from registry-1.docker.io, which some
# egress policies allow when index.docker.io is not.
mirror_images() {
  local manifest=$1 ref src name digest mirrored
  local out
  out="$(cat "${manifest}")"
  for ref in $(grep -oE 'image: [^ ]+@sha256:[0-9a-f]+' "${manifest}" | cut -d' ' -f2 | sort -u); do
    name="${ref%@*}"
    name="${name%:*}"
    digest="${ref#*@}"
    src="${ref}"
    if [[ "${name%%/*}" != *.* ]]; then
      src="registry-1.docker.io/${ref}"
    fi
    mirrored="localhost:${REGISTRY_PORT}/mirror/${name##*/}"
    crane copy "${src}" "${mirrored}:${digest#sha256:}" >&2
    out="${out//${ref}/${mirrored}@${digest}}"
  done
  printf '%s\n' "${out}"
}

# ready_pod_ip prints the IP of a ready pod labeled app=$1. A rollout leaves
# the pod it is replacing in the list until it is gone, so a pod with a
# deletion timestamp does not count. This does not use the Service: Jaeger is
# applied before its Service exists, and some nested kind clusters never
# program Service endpoints.
ready_pod_ip() {
  local ip deadline=$((SECONDS + 60))
  while ((SECONDS < deadline)); do
    ip="$(kubectl -n ci-substrate get pods -l "app=$1" -o jsonpath='{range .items[*]}{.status.conditions[?(@.type=="Ready")].status}{" "}{.metadata.deletionTimestamp}{" "}{.status.podIP}{"\n"}{end}' |
      awk '$1 == "True" && $2 ~ /^[0-9.]+$/ { print $2; exit }')"
    if [[ -n "${ip}" ]]; then
      echo "${ip}"
      return 0
    fi
    sleep 1
  done
  echo "no ready pod labeled app=$1" >&2
  return 1
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

# kube-proxy and local-path-provisioner exit with "too many open files" when
# the host's inotify instance limit is low (Linux defaults to 128) and another
# kind cluster already holds most of them. Raise the limits when permitted;
# otherwise continue, since a single cluster on a CI runner stays under them.
# See https://kind.sigs.k8s.io/docs/user/known-issues/#pod-errors-due-to-too-many-open-files
raise_inotify_limits() {
  local instances watches
  instances="$(sysctl -n fs.inotify.max_user_instances 2>/dev/null || echo 0)"
  watches="$(sysctl -n fs.inotify.max_user_watches 2>/dev/null || echo 0)"
  if [[ "${instances}" -ge 512 && "${watches}" -ge 524288 ]]; then
    return
  fi
  local sudo=""
  if [[ "$(id -u)" -ne 0 ]]; then
    command -v sudo >/dev/null 2>&1 || return 0
    sudo="sudo -n"
  fi
  ${sudo} sysctl -q -w fs.inotify.max_user_instances=512 fs.inotify.max_user_watches=524288 2>/dev/null ||
    echo "could not raise inotify limits (instances=${instances}, watches=${watches}); continuing" >&2
}

create_cluster() {
  if kind get clusters 2>/dev/null | grep -qx "${CLUSTER_NAME}"; then
    echo "Reusing kind cluster ${CLUSTER_NAME}"
    return
  fi
  raise_inotify_limits
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

mkdir -p "${WORKDIR}"
need_cmd docker
need_cmd go
need_cmd curl
install_kind
install_ko
install_kubectl
install_crane
need_cmd kind
need_cmd ko
need_cmd kubectl

ensure_registry
create_cluster
kubectl cluster-info --context "kind-${CLUSTER_NAME}" >/dev/null

export KO_DOCKER_REPO="localhost:${REGISTRY_PORT}/ci-substrate"
# Prefer the repo's chainguard bases; when that registry is unreachable
# (egress-restricted VMs), fall back to the docker.io mirrors of the same
# images, for the default base and for the runner's override in .ko.yaml.
if [[ -z "${KO_DEFAULTBASEIMAGE:-}" ]]; then
  if ! curl -fsS --max-time 3 https://cgr.dev/v2/ >/dev/null 2>&1; then
    export KO_DEFAULTBASEIMAGE=registry-1.docker.io/chainguard/static:latest
    sed 's#cgr.dev/chainguard/#registry-1.docker.io/chainguard/#' "${ROOT}/.ko.yaml" >"${WORKDIR}/.ko.yaml"
    export KO_CONFIG_PATH="${WORKDIR}/.ko.yaml"
    echo "cgr.dev unreachable; using ${KO_DEFAULTBASEIMAGE} and ${KO_CONFIG_PATH}"
  fi
fi

cd "${ROOT}"
echo "ko apply deploy/"
# Apply the static config first (no images), then the image-bearing resources
# so a ko resolve failure does not leave a half-applied namespace alone.
kubectl apply -f deploy/00-namespace-and-config.yaml

# Some nested kind environments cannot program ClusterIP rules (kube-proxy's
# iptables-restore fails without the xt_statistic module), so every in-cluster
# address below is a pod IP rather than a Service. The collector exports to
# Jaeger, and every workload exports to the collector through the otel
# ConfigMap, so Jaeger comes up first, then the collector, then the ConfigMap
# is pointed at the collector's pod.
TELEMETRY="${WORKDIR}/telemetry.yaml"
mirror_images deploy/05-telemetry.yaml >"${TELEMETRY}"
kubectl apply -f "${TELEMETRY}" -l app=jaeger
kubectl -n ci-substrate rollout status deployment/jaeger --timeout=300s
JAEGER_POD_IP="$(ready_pod_ip jaeger)"
sed "s#jaeger.ci-substrate.svc.cluster.local#${JAEGER_POD_IP}#g" "${TELEMETRY}" | kubectl apply -f -
kubectl -n ci-substrate rollout status deployment/otel-collector --timeout=300s
OTEL_POD_IP="$(ready_pod_ip otel-collector)"
echo "Using collector pod IP ${OTEL_POD_IP}:4317"
# Pods read the ConfigMap when they start, so on a reused cluster whose
# collector moved, the workloads are restarted below.
RESTART=0
old_endpoint="$(kubectl -n ci-substrate get configmap otel -o jsonpath='{.data.OTEL_EXPORTER_OTLP_ENDPOINT}' 2>/dev/null || true)"
if [[ -n "${old_endpoint}" && "${old_endpoint}" != "http://${OTEL_POD_IP}:4317" ]]; then
  RESTART=1
fi
restart_if_moved() {
  if [[ "${RESTART}" -eq 1 ]]; then
    kubectl -n ci-substrate rollout restart "$1"
  fi
}
sed "s#jaeger.ci-substrate.svc.cluster.local#${JAEGER_POD_IP}#g; s#otel-collector.ci-substrate.svc.cluster.local#${OTEL_POD_IP}#g" \
  "${TELEMETRY}" | kubectl apply -f -

ko apply -f deploy/10-cas.yaml
restart_if_moved statefulset/cas
kubectl -n ci-substrate rollout status statefulset/cas --timeout=300s

# Point cascache at the cas pod IP. Roll cascache out once, so no later
# rollout replaces the pod under a port-forward.
CAS_POD_IP="$(ready_pod_ip cas)"
echo "Using cas pod IP ${CAS_POD_IP}:8980"
ko resolve -f deploy/20-cascache.yaml \
  | sed "s#cas.ci-substrate.svc.cluster.local#${CAS_POD_IP}#g" \
  | kubectl apply -f -
restart_if_moved daemonset/cascache
kubectl -n ci-substrate rollout status daemonset/cascache --timeout=300s

# The runners dial cas and the cascache on their own node by pod IP for the
# same reason. The cascache is a DaemonSet on a one-node cluster, so its one
# pod is the node-local one.
CACHE_POD_IP="$(ready_pod_ip cascache)"
ko resolve -f deploy/40-runner.yaml \
  | sed "s#cas.ci-substrate.svc.cluster.local#${CAS_POD_IP}#g; s#cascache.ci-substrate.svc.cluster.local#${CACHE_POD_IP}#g" \
  | kubectl apply -f -
restart_if_moved deployment/runner-tenant-a
restart_if_moved deployment/runner-tenant-b
kubectl -n ci-substrate rollout status deployment/runner-tenant-a --timeout=300s
kubectl -n ci-substrate rollout status deployment/runner-tenant-b --timeout=300s

# Port-forward Services, not pods: a rollout replaces DaemonSet pod names.
LOCAL_ORIGIN_PORT=18980
LOCAL_CACHE_PORT=19092
LOCAL_METRICS_PORT=19090
LOCAL_JAEGER_PORT=16686
LOCAL_PROM_PORT=18889
kubectl -n ci-substrate port-forward svc/cas "${LOCAL_ORIGIN_PORT}:8980" >/dev/null &
PORT_FORWARD_PIDS+=($!)
kubectl -n ci-substrate port-forward svc/cascache "${LOCAL_CACHE_PORT}:9092" "${LOCAL_METRICS_PORT}:9090" >/dev/null &
PORT_FORWARD_PIDS+=($!)
kubectl -n ci-substrate port-forward svc/jaeger "${LOCAL_JAEGER_PORT}:16686" >/dev/null &
PORT_FORWARD_PIDS+=($!)
kubectl -n ci-substrate port-forward svc/otel-collector "${LOCAL_PROM_PORT}:8889" >/dev/null &
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

for port in "${LOCAL_ORIGIN_PORT}" "${LOCAL_CACHE_PORT}" "${LOCAL_METRICS_PORT}" "${LOCAL_JAEGER_PORT}" "${LOCAL_PROM_PORT}"; do
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
  -shared=shared \
  -exec-timeout=3m

echo "Building with stock Bazel as two tenants"
bash "${ROOT}/e2e/run-bazel.sh" "127.0.0.1:${LOCAL_ORIGIN_PORT}"

echo "Checking a Bazel build's trace and metrics"
bash "${ROOT}/e2e/run-telemetry.sh" "127.0.0.1:${LOCAL_ORIGIN_PORT}" \
  "127.0.0.1:${LOCAL_JAEGER_PORT}" "127.0.0.1:${LOCAL_PROM_PORT}"

if [[ "${CI_SUBSTRATE_DOGFOOD:-1}" != "0" ]]; then
  echo "Building and testing ci-substrate with Bazel on the cluster"
  bash "${ROOT}/e2e/run-dogfood.sh" "127.0.0.1:${LOCAL_ORIGIN_PORT}"
fi

echo "Runner logs:"
kubectl -n ci-substrate logs -l app=runner --tail=20 --prefix

echo "ci-substrate kind e2e passed"
