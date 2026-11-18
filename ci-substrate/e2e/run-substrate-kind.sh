#!/usr/bin/env bash
# Run the Substrate overlay end to end on a two-node kind cluster shaped like
# the GKE Standard layout in deploy/substrate/README.md:
#
#   - The control-plane node is the always-on node. It is labeled and tainted
#     ci-substrate.imjasonh.com/always-on=true, and runs Substrate, cas, the
#     pool, and the base WorkerPool.
#   - The worker node is the burst node, labeled
#     ci-substrate.imjasonh.com/burst=true. The burst WorkerPool's workers run
#     there, and so does anything that does not tolerate the always-on taint.
#
# It installs Agent Substrate from its published images with ate-setup,
# then runs run-kind.sh for the control plane and run-substrate.sh for the
# actors, which checks that the pool scales the burst WorkerPool up and back
# to zero. A kind node cannot be removed and re-added the way a node pool
# scales, so the burst node stays up; what the test checks is the WorkerPool.
#
# Needs docker, go, git, kind (tested with v0.33.0), kubectl, kubectl-ate, ko,
# crane, and python3. Set CI_SUBSTRATE_SUBSTRATE_SRC to a checkout of
# agent-substrate/substrate at SUBSTRATE_VERSION (by default the
# go.ate.dev/substrate version in go.mod); otherwise it clones one. Set
# CI_SUBSTRATE_KIND_KEEP=1 to keep the cluster and registry it creates.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLUSTER_NAME="${CI_SUBSTRATE_KIND_CLUSTER:-ci-substrate-substrate}"
WORKDIR="${TMPDIR:-/tmp}/ci-substrate-substrate-kind-$$"
SUBSTRATE_VERSION="${SUBSTRATE_VERSION:-$(cd "${ROOT}" && go list -m -f '{{.Version}}' go.ate.dev/substrate)}"
SUBSTRATE_SRC="${CI_SUBSTRATE_SUBSTRATE_SRC:-}"
# Substrate's kind install points atelet at kind-registry:5000 for every
# localhost image, so the registry container has that name.
REGISTRY_NAME=kind-registry
REGISTRY_PORT="${CI_SUBSTRATE_REGISTRY_PORT:-5312}"
ALWAYS_ON=ci-substrate.imjasonh.com/always-on
BURST=ci-substrate.imjasonh.com/burst
KIND_CREATED=0
REGISTRY_CREATED=0

cleanup() {
  if [[ "${CI_SUBSTRATE_KIND_KEEP:-}" != "1" ]]; then
    if [[ "${KIND_CREATED}" -eq 1 ]]; then
      kind delete cluster --name "${CLUSTER_NAME}" >/dev/null 2>&1 || true
    fi
    if [[ "${REGISTRY_CREATED}" -eq 1 ]]; then
      docker rm -f "${REGISTRY_NAME}" >/dev/null 2>&1 || true
    fi
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

for cmd in docker go git kind kubectl kubectl-ate ko crane python3; do
  need_cmd "${cmd}"
done
mkdir -p "${WORKDIR}"

if [[ -z "${SUBSTRATE_SRC}" ]]; then
  SUBSTRATE_SRC="${WORKDIR}/substrate"
  git clone -q --depth 1 --branch "${SUBSTRATE_VERSION}" https://github.com/agent-substrate/substrate "${SUBSTRATE_SRC}"
fi

echo "==> Registry ${REGISTRY_NAME} on 127.0.0.1:${REGISTRY_PORT}"
if ! docker inspect -f '{{.State.Running}}' "${REGISTRY_NAME}" 2>/dev/null | grep -q true; then
  docker rm -f "${REGISTRY_NAME}" >/dev/null 2>&1 || true
  docker run -d --restart=always -p "127.0.0.1:${REGISTRY_PORT}:5000" --name "${REGISTRY_NAME}" registry:2 >/dev/null
  REGISTRY_CREATED=1
fi

echo "==> kind cluster ${CLUSTER_NAME}"
if kind get clusters 2>/dev/null | grep -qx "${CLUSTER_NAME}"; then
  echo "Reusing kind cluster ${CLUSTER_NAME}"
else
  # Substrate's pod certificates need these feature gates and runtime config.
  # kube-proxy's nftables mode works on kernels without the iptables
  # statistic match, which iptables mode needs for Services with more than
  # one endpoint.
  cat >"${WORKDIR}/kind.yaml" <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
networking:
  kubeProxyMode: nftables
containerdConfigPatches:
- |-
  [plugins."io.containerd.grpc.v1.cri".registry]
    config_path = "/etc/containerd/certs.d"
featureGates:
  ClusterTrustBundle: true
  ClusterTrustBundleProjection: true
  PodCertificateRequest: true
runtimeConfig:
  "certificates.k8s.io/v1beta1": "true"
kubeadmConfigPatches:
- |
  kind: KubeletConfiguration
  serializeImagePulls: false
  maxParallelImagePulls: 4
nodes:
- role: control-plane
- role: worker
EOF
  kind create cluster --name "${CLUSTER_NAME}" --config "${WORKDIR}/kind.yaml"
  KIND_CREATED=1
fi
docker network connect kind "${REGISTRY_NAME}" 2>/dev/null || true
reg_dir="/etc/containerd/certs.d/localhost:${REGISTRY_PORT}"
for node in $(kind get nodes --name "${CLUSTER_NAME}"); do
  # gVisor sandboxes reach other pods through proxy ARP on the node.
  docker exec "${node}" sysctl -q net.ipv4.conf.all.proxy_arp=1
  docker exec "${node}" mkdir -p "${reg_dir}"
  docker exec -i "${node}" tee "${reg_dir}/hosts.toml" >/dev/null <<EOF
[host."http://${REGISTRY_NAME}:5000"]
  capabilities = ["pull", "resolve"]
EOF
done

kind get kubeconfig --name "${CLUSTER_NAME}" >"${WORKDIR}/kubeconfig"
export KUBECONFIG="${WORKDIR}/kubeconfig"
CONTROL_PLANE="${CLUSTER_NAME}-control-plane"
WORKER="${CLUSTER_NAME}-worker"

echo "==> ${CONTROL_PLANE} is always on, ${WORKER} is burst"
kubectl taint node "${CONTROL_PLANE}" node-role.kubernetes.io/control-plane:NoSchedule- 2>/dev/null || true
kubectl label node "${CONTROL_PLANE}" "${ALWAYS_ON}=true" --overwrite
kubectl label node "${WORKER}" "${BURST}=true" --overwrite

# Substrate's postgres and object store keep their data on local-path volumes,
# which bind to the node they first ran on. The worker is tainted while
# Substrate installs, so those volumes are on the always-on node.
SUBSTRATE_NAMESPACES=(ate-system otel-system podcertificate-controller-system)
echo "==> Agent Substrate ${SUBSTRATE_VERSION}"
if ! kubectl -n ate-system get deployment ate-api-server >/dev/null 2>&1; then
  kubectl taint node "${WORKER}" ci-substrate.imjasonh.com/installing=true:NoSchedule --overwrite
  (
    cd "${SUBSTRATE_SRC}"
    ATE_INSTALL_KIND=true KIND_CLUSTER_NAME="${CLUSTER_NAME}" KUBECONFIG="${KUBECONFIG}" \
      go run ./cmd/ate-setup deploy ate-system \
      --credential-provider='{"name":"k8s.io"}' \
      --ingress-allowed-spiffe-ids=spiffe://cluster.local/ns/ate-system/sa/atenet-client \
      --image-repo ghcr.io/agent-substrate/substrate \
      --image-tag "${SUBSTRATE_VERSION}" \
      --sandbox-classes=gvisor
  )
fi
kubectl taint node "${WORKER}" ci-substrate.imjasonh.com/installing- 2>/dev/null || true
kubectl taint node "${CONTROL_PLANE}" "${ALWAYS_ON}=true:NoSchedule" --overwrite

echo "==> Substrate's control plane on ${CONTROL_PLANE}"
# DaemonSets such as atelet must run on both nodes, so they get the toleration
# without the nodeSelector.
pin_always_on() {
  python3 -c '
import json, sys
key = sys.argv[1]
obj = json.load(sys.stdin)
spec = obj["spec"]["template"]["spec"]
tolerations = spec.setdefault("tolerations", [])
if not any(t.get("key") == key for t in tolerations):
    tolerations.append({"key": key, "operator": "Exists", "effect": "NoSchedule"})
if obj["kind"] != "DaemonSet":
    spec.setdefault("nodeSelector", {})[key] = "true"
obj.pop("status", None)
for field in ("resourceVersion", "uid", "creationTimestamp", "generation", "managedFields"):
    obj["metadata"].pop(field, None)
print(json.dumps(obj))
' "${ALWAYS_ON}"
}
for ns in "${SUBSTRATE_NAMESPACES[@]}"; do
  for workload in deployment statefulset daemonset; do
    for name in $(kubectl -n "${ns}" get "${workload}" -o name); do
      kubectl -n "${ns}" get "${name}" -o json | pin_always_on | kubectl replace -f - >/dev/null
    done
  done
done
for ns in "${SUBSTRATE_NAMESPACES[@]}"; do
  for workload in deployment statefulset daemonset; do
    for name in $(kubectl -n "${ns}" get "${workload}" -o name); do
      kubectl -n "${ns}" rollout status "${name}" --timeout=300s
    done
  done
done
off="$(kubectl get pods -A -o json | python3 -c '
import json, sys
node, namespaces = sys.argv[1], sys.argv[2:]
for p in json.load(sys.stdin)["items"]:
    meta = p["metadata"]
    owners = [o["kind"] for o in meta.get("ownerReferences", [])]
    if (meta["namespace"] in namespaces and "DaemonSet" not in owners
            and "Job" not in owners and "deletionTimestamp" not in meta
            and p["status"].get("phase") == "Running"
            and p["spec"].get("nodeName") != node):
        print(meta["namespace"], meta["name"], p["spec"].get("nodeName"))
' "${CONTROL_PLANE}" "${SUBSTRATE_NAMESPACES[@]}")"
if [[ -n "${off}" ]]; then
  echo "Substrate pods off the always-on node:" >&2
  echo "${off}" >&2
  exit 1
fi

echo "==> ci-substrate control plane"
# This script's cleanup, not run-kind.sh's, removes the cluster and registry.
CI_SUBSTRATE_KIND_CLUSTER="${CLUSTER_NAME}" \
  CI_SUBSTRATE_REGISTRY_NAME="${REGISTRY_NAME}" \
  CI_SUBSTRATE_REGISTRY_PORT="${REGISTRY_PORT}" \
  CI_SUBSTRATE_KIND_KEEP=1 \
  CI_SUBSTRATE_DOGFOOD="${CI_SUBSTRATE_DOGFOOD:-0}" \
  bash "${ROOT}/e2e/run-kind.sh"

for app in cas otel-collector jaeger; do
  node="$(kubectl -n ci-substrate get pods -l "app=${app}" -o jsonpath='{.items[0].spec.nodeName}')"
  if [[ "${node}" != "${CONTROL_PLANE}" ]]; then
    echo "${app} runs on ${node}, want the always-on node ${CONTROL_PLANE}" >&2
    exit 1
  fi
done

echo "==> Substrate actors"
KO_DOCKER_REPO="localhost:${REGISTRY_PORT}/ci-substrate" bash "${ROOT}/e2e/run-substrate.sh"

echo "ci-substrate Substrate kind e2e passed"
