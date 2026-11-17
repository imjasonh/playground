#!/usr/bin/env bash
# Run tenant-a's CI runners as Substrate actors. Needs a cluster with Agent
# Substrate installed (with the k8s.io credential provider) and the cas and
# cascache control plane from deploy/ already running; run-kind.sh with
# CI_SUBSTRATE_KIND_KEEP=1 leaves such a control plane behind, and the
# Substrate install is documented in deploy/substrate/README.md. Needs
# kubectl, kubectl-ate, ko, and KO_DOCKER_REPO.
#
# atelet pulls actor images itself, from inside its pod, so the registry in
# the template must be reachable from pods. A kind registry published on
# 127.0.0.1 is not; set CI_SUBSTRATE_ACTOR_IMAGE_REPO to a repository that
# is, and the template is resolved against that one. Set
# CI_SUBSTRATE_ATEWORKER_IMAGE to a mirror of the ateworker-gvisor image when
# the cluster cannot pull from ghcr.io.
#
# It creates the tenant-a atespace, the token Secret the egress gateway
# injects, the credential provider's grant of that Secret's namespace to the
# atespace, the WorkerPool, the casfs CSI driver with tenant-a's
# StorageClass, the runner ActorTemplate, and the pool Deployment. External
# volumes are behind Substrate's ExternalVolumes preview gate, so it turns
# that on in ate-api-server. Then it runs cictl against cas and checks that
# an actor executed the action (the ActionResult's worker is an actor name,
# not a Deployment runner) and read its inputs from the casfs volume.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OVERLAY="${ROOT}/deploy/substrate"
WORKDIR="${TMPDIR:-/tmp}/ci-substrate-substrate-e2e-$$"
ATESPACE=tenant-a
# The runner Deployment from deploy/40-runner.yaml also leases tenant-a's
# actions. Scale it down so actors do the work this script checks.
RUNNER_DEPLOYMENT="${CI_SUBSTRATE_RUNNER_DEPLOYMENT:-runner-tenant-a}"
WORKER_IMAGE="${CI_SUBSTRATE_ATEWORKER_IMAGE:-}"
ACTOR_IMAGE_REPO="${CI_SUBSTRATE_ACTOR_IMAGE_REPO:-${KO_DOCKER_REPO:-}}"
PORT_FORWARD_PIDS=()

cleanup() {
  local pid
  for pid in "${PORT_FORWARD_PIDS[@]:-}"; do
    if [[ -n "${pid}" ]] && kill -0 "${pid}" 2>/dev/null; then
      kill "${pid}" 2>/dev/null || true
      wait "${pid}" 2>/dev/null || true
    fi
  done
  rm -rf "${WORKDIR}"
}
trap cleanup EXIT

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

need_cmd kubectl
need_cmd kubectl-ate
need_cmd ko
: "${KO_DOCKER_REPO:?set KO_DOCKER_REPO to the registry the cluster pulls from}"
mkdir -p "${WORKDIR}"
# Same base-image fallback as run-kind.sh for VMs that cannot reach cgr.dev.
if [[ -z "${KO_DEFAULTBASEIMAGE:-}" ]]; then
  if ! curl -fsS --max-time 3 https://cgr.dev/v2/ >/dev/null 2>&1; then
    export KO_DEFAULTBASEIMAGE=registry-1.docker.io/chainguard/static:latest
    sed 's#cgr.dev/chainguard/#registry-1.docker.io/chainguard/#' "${ROOT}/.ko.yaml" >"${WORKDIR}/.ko.yaml"
    export KO_CONFIG_PATH="${WORKDIR}/.ko.yaml"
  fi
fi

echo "==> Tenant ${ATESPACE}: atespace, token Secret, credential grant"
if ! kubectl ate get atespaces -o json | grep -q "\"name\": *\"${ATESPACE}\""; then
  kubectl ate create atespace "${ATESPACE}"
fi
kubectl apply -f "${OVERLAY}/tenant-a-token.yaml"
# The credential provider's namespace policy is one ConfigMap for every
# atespace, so it is edited, not applied.
kubectl -n ate-system get configmap k8s-credential-provider-namespace-policy -o jsonpath='{.data.namespace-policy\.yaml}' >"${WORKDIR}/policy.yaml"
if ! grep -q "atespace: ${ATESPACE}$" "${WORKDIR}/policy.yaml"; then
  if grep -q '^policies: \[\]' "${WORKDIR}/policy.yaml"; then
    sed -i 's/^policies: \[\]/policies:/' "${WORKDIR}/policy.yaml"
  fi
  printf -- '- atespace: %s\n  allowedNamespaces:\n  - ci-substrate-%s\n' "${ATESPACE}" "${ATESPACE}" >>"${WORKDIR}/policy.yaml"
  kubectl -n ate-system create configmap k8s-credential-provider-namespace-policy \
    --from-file=namespace-policy.yaml="${WORKDIR}/policy.yaml" --dry-run=client -o yaml | kubectl apply -f -
  kubectl -n ate-system rollout restart deployment/k8s-credential-provider
  kubectl -n ate-system rollout status deployment/k8s-credential-provider --timeout=120s
fi

echo "==> WorkerPool"
if [[ -n "${WORKER_IMAGE}" ]]; then
  sed "s#ghcr.io/agent-substrate/substrate/ateworker-gvisor:v1.0.0#${WORKER_IMAGE}#" "${OVERLAY}/workerpool.yaml" | kubectl apply -f -
else
  kubectl apply -f "${OVERLAY}/workerpool.yaml"
fi
kubectl -n ci-substrate-workers rollout status deployment/ci-runner --timeout=300s

echo "==> ExternalVolumes preview gate"
# ate-api-server takes --preview=<gate,...>. The template's external volume
# needs ExternalVolumes on.
preview="$(kubectl -n ate-system get deployment ate-api-server -o json |
  python3 -c 'import json,sys; print(next((a for c in json.load(sys.stdin)["spec"]["template"]["spec"]["containers"] for a in c["args"] if a.startswith("--preview=")), ""))')"
if [[ "${preview}" != *ExternalVolumes* ]]; then
  if [[ -z "${preview}" || "${preview}" == "--preview=" ]]; then
    want="--preview=ExternalVolumes"
  else
    want="${preview},ExternalVolumes"
  fi
  kubectl -n ate-system get deployment ate-api-server -o json |
    python3 -c "import json,sys
d=json.load(sys.stdin)
for c in d['spec']['template']['spec']['containers']:
    c['args']=[a for a in c['args'] if not a.startswith('--preview=')]
    if c['name']=='ate-api-server' or len(d['spec']['template']['spec']['containers'])==1:
        c['args'].append('${want}')
print(json.dumps(d))" | kubectl apply -f -
  kubectl -n ate-system rollout status deployment/ate-api-server --timeout=180s
fi

echo "==> casfs CSI driver: viewer in ${ATESPACE}"
# The driver asks Substrate which atespace an actor is in, as its own
# ServiceAccount, and refuses a volume for an actor outside the StorageClass's
# atespace. It needs only the viewer role, and only here.
driver_member="user:system:serviceaccount:ci-substrate:casfs-csi"
if ! kubectl ate get access-policy -a "${ATESPACE}" -o json >"${WORKDIR}/access-policy.json" 2>/dev/null ||
  ! grep -q '"bindings"' "${WORKDIR}/access-policy.json"; then
  printf 'bindings:\n- role: viewer\n  members:\n  - %s\n' "${driver_member}" >"${WORKDIR}/access-policy-new.yaml"
  kubectl ate create access-policy -a "${ATESPACE}" -f "${WORKDIR}/access-policy-new.yaml"
elif ! grep -q "${driver_member}" "${WORKDIR}/access-policy.json"; then
  python3 - "${WORKDIR}/access-policy.json" "${driver_member}" <<'PY' >"${WORKDIR}/access-policy-new.json"
import json, sys
policy = json.load(open(sys.argv[1]))
bindings = policy.setdefault("bindings", [])
viewer = next((b for b in bindings if b.get("role") == "viewer"), None)
if viewer is None:
    viewer = {"role": "viewer", "members": []}
    bindings.append(viewer)
viewer.setdefault("members", []).append(sys.argv[2])
print(json.dumps(policy))
PY
  kubectl ate update access-policy -a "${ATESPACE}" -f "${WORKDIR}/access-policy-new.json"
fi

echo "==> casfs CSI driver"
# A StorageClass's parameters are immutable, so an older class without the
# atespace parameter is replaced.
if kubectl get storageclass casfs-tenant-a >/dev/null 2>&1 &&
  [[ -z "$(kubectl get storageclass casfs-tenant-a -o jsonpath='{.parameters.atespace}')" ]]; then
  kubectl delete storageclass casfs-tenant-a
fi
ko apply -f "${OVERLAY}/casfs-csi.yaml"
kubectl -n ci-substrate rollout status daemonset/casfs-csi --timeout=180s

echo "==> Runner ActorTemplate"
KO_DOCKER_REPO="${ACTOR_IMAGE_REPO}" ko resolve -f "${OVERLAY}/runner-template.yaml" >"${WORKDIR}/runner-template.yaml"
# Templates are immutable, so a changed template is recreated. An actor keeps
# the volumes it was created with, so an actor from the old template cannot
# resume against the new one; the old actors go too, with the pool stopped
# so it does not make more against the old template. ko apply of pool.yaml
# brings the pool back.
if kubectl ate get actor-templates -a "${ATESPACE}" -o json | grep -q '"name": *"ci-runner"'; then
  if kubectl -n ate-system get deployment ci-substrate-pool-tenant-a >/dev/null 2>&1; then
    kubectl -n ate-system scale deployment ci-substrate-pool-tenant-a --replicas=0
    kubectl -n ate-system rollout status deployment/ci-substrate-pool-tenant-a --timeout=120s
  fi
  for actor in $(kubectl ate get actors -a "${ATESPACE}" -o json |
    python3 -c 'import json,sys; print(" ".join(a["metadata"]["name"] for a in json.load(sys.stdin).get("actors", []) if a.get("actorTemplate", {}).get("name") == "ci-runner"))'); do
    kubectl ate delete actor "${actor}" -a "${ATESPACE}"
  done
  kubectl ate delete actor-template ci-runner -a "${ATESPACE}"
fi
kubectl ate --preview create actor-template -f "${WORKDIR}/runner-template.yaml"

echo "==> Pool"
kubectl -n ate-system create configmap ci-substrate-pool-tenant-a \
  --from-file=egress-policy.yaml="${OVERLAY}/egress-cas.yaml" --dry-run=client -o yaml | kubectl apply -f -
ko apply -f "${OVERLAY}/pool.yaml"
kubectl -n ate-system rollout status deployment/ci-substrate-pool-tenant-a --timeout=180s
if kubectl -n ci-substrate get deployment "${RUNNER_DEPLOYMENT}" >/dev/null 2>&1; then
  kubectl -n ci-substrate scale deployment "${RUNNER_DEPLOYMENT}" --replicas=0
fi

echo "==> Waiting for a warm actor"
for _ in $(seq 1 60); do
  if kubectl ate get actors -a "${ATESPACE}" 2>/dev/null | grep -q 'ci-runner-'; then
    break
  fi
  sleep 2
done
kubectl ate get actors -a "${ATESPACE}"

echo "==> Executing an action through the pool"
kubectl -n ci-substrate port-forward svc/cas 18980:8980 >/dev/null 2>&1 &
PORT_FORWARD_PIDS+=("$!")
kubectl -n ci-substrate port-forward svc/cascache 19092:9092 >/dev/null 2>&1 &
PORT_FORWARD_PIDS+=("$!")
sleep 2
go run "${ROOT}/cmd/cictl" -origin-addr=localhost:18980 -cache-addr=localhost:19092 -exec-timeout=5m -worker-prefix=ci-runner- -expect-input-mode=volume run
echo "==> Actors after the run"
kubectl ate get actors -a "${ATESPACE}"
kubectl -n ate-system logs deployment/ci-substrate-pool-tenant-a --tail=20

echo "==> Another atespace's template naming ${ATESPACE}'s StorageClass gets no volume"
# Substrate lets any template name any StorageClass. The driver is what
# refuses: an actor in the intruder atespace has no volume of casfs-tenant-a.
INTRUDER=intruder
intruder_cleanup() {
  kubectl ate delete actor probe -a "${INTRUDER}" >/dev/null 2>&1 || true
  kubectl ate delete actor-template ci-runner -a "${INTRUDER}" >/dev/null 2>&1 || true
  kubectl ate delete atespace "${INTRUDER}" >/dev/null 2>&1 || true
}
intruder_cleanup
kubectl ate create atespace "${INTRUDER}"
sed "s/atespace: ${ATESPACE}$/atespace: ${INTRUDER}/" "${WORKDIR}/runner-template.yaml" >"${WORKDIR}/intruder-template.yaml"
kubectl ate --preview create actor-template -f "${WORKDIR}/intruder-template.yaml"
kubectl ate --preview create actor probe -a "${INTRUDER}" --template ci-runner
if resume_out="$(kubectl ate --preview resume actor probe -a "${INTRUDER}" 2>&1)"; then
  echo "an actor in ${INTRUDER} resumed with ${ATESPACE}'s StorageClass" >&2
  intruder_cleanup
  exit 1
fi
if ! grep -q 'PermissionDenied.*not in atespace' <<<"${resume_out}"; then
  echo "resume failed, but not on the atespace policy: ${resume_out}" >&2
  intruder_cleanup
  exit 1
fi
echo "refused: ${resume_out##*desc = }"
intruder_cleanup
