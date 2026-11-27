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
# the cluster cannot pull from ghcr.io. Set CI_SUBSTRATE_WORKER_REQUESTS to a
# resource list such as "{cpu: 100m, memory: 512Mi}" to give the worker pods
# requests below their limits; Substrate sizes a worker from its limits alone.
#
# The WorkerPools in workerpool.yaml need a node labeled
# ci-substrate.imjasonh.com/always-on=true (it may carry the matching taint)
# and a node labeled ci-substrate.imjasonh.com/burst=true;
# run-substrate-kind.sh makes a kind cluster with both.
#
# It creates the tenant-a atespace, the token Secret the egress gateway
# injects, the credential provider's grant of that Secret's namespace to the
# atespace, the WorkerPools, the casfs CSI driver with tenant-a's
# StorageClass, the runner ActorTemplate, and the pool Deployment. External
# volumes are behind Substrate's ExternalVolumes preview gate, so it turns
# that on in ate-api-server. Then it runs the Go e2e tests against cas and checks that
# an actor executed the action (the ActionResult's worker is an actor name,
# not a Deployment runner) and read its inputs from the casfs volume. Last,
# it checks that the pool sizes the burst WorkerPool: zero workers while the
# base worker has room, one when a third actor needs it, and zero again once
# that actor is suspended.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OVERLAY="${ROOT}/deploy/substrate"
WORKDIR="${TMPDIR:-/tmp}/ci-substrate-substrate-e2e-$$"
ATESPACE=tenant-a
# The runner Deployment from deploy/40-runner.yaml also leases tenant-a's
# actions. Scale it down so actors do the work this script checks.
RUNNER_DEPLOYMENT="${CI_SUBSTRATE_RUNNER_DEPLOYMENT:-runner-tenant-a}"
WORKER_IMAGE="${CI_SUBSTRATE_ATEWORKER_IMAGE:-}"
WORKER_REQUESTS="${CI_SUBSTRATE_WORKER_REQUESTS:-}"
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

echo "==> Tenant ${ATESPACE}: atespace"
if ! kubectl ate get atespaces -o json | grep -q "\"name\": *\"${ATESPACE}\""; then
  kubectl ate create atespace "${ATESPACE}"
fi

echo "==> Configure cas for Substrate Actor JWT verification"
# Mount Substrate's servicedns ClusterTrustBundle into cas so it can verify
# ate-idp-server's TLS certificate for OIDC discovery / JWKS, and enable
# Actor JWT verification for actors calling cas via atenet-egress.
kubectl -n ci-substrate get statefulset cas -o json | python3 -c '
import json, sys
s = json.load(sys.stdin)
pod = s["spec"]["template"]["spec"]
vols = pod.setdefault("volumes", [])
if not any(v.get("name") == "ate-trust" for v in vols):
    vols.append({
        "name": "ate-trust",
        "projected": {
            "sources": [{
                "clusterTrustBundle": {
                    "signerName": "servicedns.podcert.ate.dev/identity",
                    "labelSelector": {"matchLabels": {"podcert.ate.dev/canarying": "live"}},
                    "path": "trust-bundle.pem",
                }
            }]
        },
    })
c = pod["containers"][0]
mounts = c.setdefault("volumeMounts", [])
if not any(m.get("name") == "ate-trust" for m in mounts):
    mounts.append({"name": "ate-trust", "mountPath": "/run/ate", "readOnly": True})
env = {e["name"]: e for e in c.get("env", [])}
for k, v in (
    ("ACTOR_JWT_ISSUER", "https://idp.ate-system.svc"),
    ("ACTOR_JWT_AUDIENCE", "cas.ci-substrate.svc.cluster.local"),
    ("ACTOR_JWT_CA_FILE", "/run/ate/trust-bundle.pem"),
):
    env[k] = {"name": k, "value": v}
c["env"] = list(env.values())
s.pop("status", None)
for f in ("resourceVersion", "uid", "creationTimestamp", "generation", "managedFields"):
    s["metadata"].pop(f, None)
print(json.dumps(s))
' | kubectl replace -f - >/dev/null
kubectl -n ci-substrate rollout status statefulset/cas --timeout=180s
# run-kind.sh points cascache at cas's pod IP; update it after cas restarts.
cas_ip="$(kubectl -n ci-substrate get pod cas-0 -o jsonpath='{.status.podIP}')"
if [[ -n "${cas_ip}" ]] && kubectl -n ci-substrate get daemonset cascache >/dev/null 2>&1; then
  cur_origin="$(kubectl -n ci-substrate get daemonset cascache -o jsonpath='{.spec.template.spec.containers[0].env[?(@.name=="ORIGIN_ADDR")].value}')"
  if [[ -n "${cur_origin}" && "${cur_origin}" != *svc.cluster.local* && "${cur_origin}" != "${cas_ip}:8980" ]]; then
    kubectl -n ci-substrate set env daemonset/cascache "ORIGIN_ADDR=${cas_ip}:8980"
    kubectl -n ci-substrate rollout status daemonset/cascache --timeout=180s
  fi
fi

echo "==> WorkerPool"
workerpool_edits=()
if [[ -n "${WORKER_IMAGE}" ]]; then
  workerpool_edits+=(-e "s#ghcr.io/agent-substrate/substrate/ateworker-gvisor:[^[:space:]]*#${WORKER_IMAGE}#")
fi
if [[ -n "${WORKER_REQUESTS}" ]]; then
  workerpool_edits+=(-e "s#^\([[:space:]]*\)limits: #\1requests: ${WORKER_REQUESTS}\n&#")
fi
sed -e '' "${workerpool_edits[@]}" "${OVERLAY}/workerpool.yaml" | kubectl apply -f -
kubectl -n ci-substrate-workers rollout status deployment/ci-runner-base --timeout=300s || {
  kubectl -n ci-substrate-workers get pods -o wide || true
  kubectl -n ci-substrate-workers describe pods | tail -40 || true
  kubectl describe nodes | grep -A12 'Allocated resources' || true
  exit 1
}

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

echo "==> Access policy in ${ATESPACE} (casfs-csi viewer, pool editor) and API access label"
# Substrate's built-in ate-api-server NetworkPolicy admits non-worker pods from
# namespaces labeled ate.dev/api-access=true.
kubectl label namespace ci-substrate ate.dev/api-access=true --overwrite
# The driver asks Substrate which atespace an actor is in (needs only viewer),
# and the pool manages actors and egress policies in this atespace (needs editor).
driver_member="user:system:serviceaccount:ci-substrate:casfs-csi"
pool_member="user:system:serviceaccount:ci-substrate:ci-substrate-pool-tenant-a"
if ! kubectl ate get access-policy -a "${ATESPACE}" -o json >"${WORKDIR}/access-policy.json" 2>/dev/null ||
  ! grep -q '"bindings"' "${WORKDIR}/access-policy.json"; then
  cat >"${WORKDIR}/access-policy-new.yaml" <<EOF
bindings:
- role: viewer
  members:
  - ${driver_member}
- role: editor
  members:
  - ${pool_member}
EOF
  kubectl ate create access-policy -a "${ATESPACE}" -f "${WORKDIR}/access-policy-new.yaml"
else
  if python3 - "${WORKDIR}/access-policy.json" "${WORKDIR}/access-policy-new.json" "${driver_member}" "${pool_member}" <<'PY'
import json, sys
src, dst, driver, pool = sys.argv[1:5]
policy = json.load(open(src))
bindings = policy.setdefault("bindings", [])
changed = False
for role, member in (("viewer", driver), ("editor", pool)):
    binding = next((b for b in bindings if b.get("role") == role), None)
    if binding is None:
        binding = {"role": role, "members": []}
        bindings.append(binding)
    members = binding.setdefault("members", [])
    if member not in members:
        members.append(member)
        changed = True
if changed:
    with open(dst, "w") as f:
        json.dump(policy, f)
    sys.exit(0)
sys.exit(1)
PY
  then
    kubectl ate update access-policy -a "${ATESPACE}" -f "${WORKDIR}/access-policy-new.json"
  fi
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
  if kubectl -n ci-substrate get deployment ci-substrate-pool-tenant-a >/dev/null 2>&1; then
    kubectl -n ci-substrate scale deployment ci-substrate-pool-tenant-a --replicas=0
    kubectl -n ci-substrate rollout status deployment/ci-substrate-pool-tenant-a --timeout=120s
  fi
  for actor in $(kubectl ate get actors -a "${ATESPACE}" -o json |
    python3 -c 'import json,sys; print(" ".join(a["metadata"]["name"] for a in json.load(sys.stdin).get("actors", []) if a.get("actorTemplate", {}).get("name") == "ci-runner"))'); do
    kubectl ate delete actor "${actor}" -a "${ATESPACE}"
  done
  kubectl ate delete actor-template ci-runner -a "${ATESPACE}"
fi
kubectl ate --preview create actor-template -f "${WORKDIR}/runner-template.yaml"
KO_DOCKER_REPO="${ACTOR_IMAGE_REPO}" ko resolve -f "${OVERLAY}/runner-env-template.yaml" >"${WORKDIR}/runner-env-template.yaml"
if kubectl ate get actor-templates -a "${ATESPACE}" -o json | grep -q '"name": *"ci-runner-env"'; then
  for actor in $(kubectl ate get actors -a "${ATESPACE}" -o json |
    python3 -c 'import json,sys; print(" ".join(a["metadata"]["name"] for a in json.load(sys.stdin).get("actors", []) if a.get("actorTemplate", {}).get("name") == "ci-runner-env"))'); do
    kubectl ate delete actor "${actor}" -a "${ATESPACE}"
  done
  kubectl ate delete actor-template ci-runner-env -a "${ATESPACE}"
fi
kubectl ate create actor-template -f "${WORKDIR}/runner-env-template.yaml"
# Verify golden snapshots are enabled and wait for the template controller to
# build the golden memory snapshot tag before the pool creates actors, so
# every actor forks from the golden snapshot instead of cold-booting.
golden="$(kubectl ate get actor-templates -a "${ATESPACE}" -o json | python3 -c '
import json, sys
for t in json.load(sys.stdin).get("actorTemplates", []):
    if t["metadata"]["name"] == "ci-runner":
        print(t.get("snapshotConfig", {}).get("goldenSnapshotConfig", {}).get("mode", "-"))
')"
if [[ "${golden}" != GOLDEN_SNAPSHOT_MODE_ENABLED ]]; then
  echo "the runner template's golden snapshot mode is ${golden}, want GOLDEN_SNAPSHOT_MODE_ENABLED" >&2
  exit 1
fi
echo "==> Waiting for golden snapshot on ci-runner template"
golden_start="${SECONDS}"
golden_tag=""
for _ in $(seq 1 90); do
  read -r golden_tag golden_err < <(kubectl ate get actor-templates -a "${ATESPACE}" -o json | python3 -c '
import json, sys
for t in json.load(sys.stdin).get("actorTemplates", []):
    if t["metadata"]["name"] == "ci-runner":
        gs = t.get("status", {}).get("goldenSnapshotStatus", {})
        tag = gs.get("goldenTag", {}).get("name", "")
        err = gs.get("errorMessage", "").replace("\n", " ")
        print(tag or "-", err or "-")
        break
else:
    print("- -")
')
  if [[ "${golden_err}" != "-" ]]; then
    echo "golden snapshot build failed: ${golden_err}" >&2
    exit 1
  fi
  if [[ "${golden_tag}" != "-" ]]; then
    echo "golden snapshot ready: tag=${golden_tag} ($((SECONDS - golden_start))s)"
    break
  fi
  sleep 2
done
if [[ "${golden_tag}" == "-" || -z "${golden_tag}" ]]; then
  echo "golden snapshot did not become ready in 180s" >&2
  kubectl ate get actor-templates -a "${ATESPACE}" -o yaml >&2 || true
  exit 1
fi

echo "==> Pool"
kubectl -n ci-substrate create configmap ci-substrate-pool-tenant-a \
  --from-file=egress-policy.yaml="${OVERLAY}/egress-cas.yaml" --dry-run=client -o yaml | kubectl apply -f -
ko apply -f "${OVERLAY}/pool.yaml"
kubectl -n ci-substrate rollout status deployment/ci-substrate-pool-tenant-a --timeout=180s
if kubectl -n ci-substrate get deployment "${RUNNER_DEPLOYMENT}" >/dev/null 2>&1; then
  kubectl -n ci-substrate scale deployment "${RUNNER_DEPLOYMENT}" --replicas=0
fi

pool_diagnostics() {
  kubectl ate get actors -a "${ATESPACE}" >&2 || true
  kubectl -n ci-substrate get pods -l app=ci-substrate-pool -o wide >&2 || true
  kubectl -n ci-substrate logs deployment/ci-substrate-pool-tenant-a --tail=60 >&2 || true
  kubectl -n ci-substrate-workers get pods -o wide >&2 || true
  kubectl -n ci-substrate-workers logs deployment/ci-runner-base --all-containers --tail=40 >&2 || true
}

echo "==> Waiting for a warm actor"
warm=""
for _ in $(seq 1 60); do
  if kubectl ate get actors -a "${ATESPACE}" 2>/dev/null | grep -q 'ci-runner-'; then
    warm=1
    break
  fi
  sleep 2
done
if [[ -z "${warm}" ]]; then
  echo "the pool made no actor in 120s" >&2
  pool_diagnostics
  exit 1
fi
kubectl ate get actors -a "${ATESPACE}"

echo "==> Executing an action through the pool"
kubectl -n ci-substrate port-forward svc/cas 18980:8980 >/dev/null 2>&1 &
PORT_FORWARD_PIDS+=("$!")
kubectl -n ci-substrate port-forward svc/cascache 19092:9092 >/dev/null 2>&1 &
PORT_FORWARD_PIDS+=("$!")
sleep 2
CI_SUBSTRATE_E2E_ORIGIN_ADDR=localhost:18980 \
CI_SUBSTRATE_E2E_CACHE_ADDR=localhost:19092 \
CI_SUBSTRATE_E2E_EXEC_TIMEOUT=5m \
CI_SUBSTRATE_E2E_WORKER_PREFIX=ci-runner- \
CI_SUBSTRATE_E2E_EXPECT_INPUT_MODE=volume \
CI_SUBSTRATE_E2E_ACTOR_JWT=1 \
  go test -v -count=1 -run '^TestE2E' "${ROOT}/e2e" || {
  pool_diagnostics
  exit 1
}
echo "==> Actors after the run"
kubectl ate get actors -a "${ATESPACE}"
kubectl -n ci-substrate logs deployment/ci-substrate-pool-tenant-a --tail=20

echo "==> Forking a pre-warmed build environment from a Substrate Tag (ci-substrate/env=warm-env)"
warm_marker="prewarmed-toolchain-v1"
warm_actor="ci-runner-env-warm-env-seed--0"
kubectl ate delete actor "${warm_actor}" -a "${ATESPACE}" >/dev/null 2>&1 || true
kubectl ate create actor "${warm_actor}" -a "${ATESPACE}" --template ci-runner-env
kubectl ate create egress-policy "${warm_actor}" -a "${ATESPACE}" -f "${OVERLAY}/egress-cas.yaml"
kubectl ate resume actor "${warm_actor}" -a "${ATESPACE}"
go run "${ROOT}/cmd/rbe-run" \
  -addr localhost:18980 -instance "${ATESPACE}" -token tok-a -runs 1 \
  -platform "ci-substrate/env=warm-env-seed" \
  -script "printf '%s' '${warm_marker}' > /var/tmp/ci-substrate-warm-env && cat /system/name"
echo "seeded /var/tmp/ci-substrate-warm-env in actor ${warm_actor}; suspending to tag"
kubectl ate suspend actor "${warm_actor}" -a "${ATESPACE}"
for _ in $(seq 1 60); do
  st="$(kubectl ate get actor "${warm_actor}" -a "${ATESPACE}" -o json | python3 -c 'import json,sys; print(json.load(sys.stdin).get("status",{}).get("state",""))')"
  if [[ "${st}" == "ACTOR_STATE_SUSPENDED" ]]; then
    break
  fi
  sleep 2
done
kubectl ate delete tag warm-env -a "${ATESPACE}" >/dev/null 2>&1 || true
kubectl ate create tag warm-env -a "${ATESPACE}" --actor "${warm_actor}" --scope atespace
CI_SUBSTRATE_E2E_ORIGIN_ADDR=localhost:18980 \
CI_SUBSTRATE_E2E_CACHE_ADDR=localhost:19092 \
CI_SUBSTRATE_E2E_EXEC_TIMEOUT=5m \
CI_SUBSTRATE_E2E_ENV_TAG=warm-env \
CI_SUBSTRATE_E2E_ENV_MARKER="${warm_marker}" \
  go test -v -count=1 -run '^TestE2ESourceTagForkedEnv$' "${ROOT}/e2e" || {
  pool_diagnostics
  exit 1
}
kubectl ate delete actor "${warm_actor}" -a "${ATESPACE}" >/dev/null 2>&1 || true

echo "==> Clean-room per-action isolation (ci-substrate/isolation=clean via RevertActor)"
CI_SUBSTRATE_E2E_ORIGIN_ADDR=localhost:18980 \
CI_SUBSTRATE_E2E_CACHE_ADDR=localhost:19092 \
CI_SUBSTRATE_E2E_EXEC_TIMEOUT=5m \
CI_SUBSTRATE_E2E_CLEAN_ISOLATION=1 \
  go test -v -count=1 -run '^TestE2ECleanRoomIsolation$' "${ROOT}/e2e" || {
  pool_diagnostics
  exit 1
}

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

echo "==> The pool sizes the burst WorkerPool"
burst_replicas() {
  kubectl -n ci-substrate-workers get workerpool ci-runner -o jsonpath='{.spec.replicas}'
}
await_burst() {
  local want=$1 timeout=$2 got deadline
  deadline=$((SECONDS + timeout))
  while ((SECONDS < deadline)); do
    got="$(burst_replicas)"
    if [[ "${got}" == "${want}" ]]; then
      return 0
    fi
    sleep 2
  done
  echo "the burst WorkerPool has ${got} replicas after ${timeout}s, want ${want}" >&2
  kubectl ate get actors -a "${ATESPACE}" >&2 || true
  kubectl -n ci-substrate logs deployment/ci-substrate-pool-tenant-a --tail=40 >&2
  return 1
}
# burst_actor_placement prints "<name> <state> <workerPool> <node>" for any
# ci-runner-* actor currently placed on the burst WorkerPool.
burst_actor_placement() {
  kubectl ate get actors -a "${ATESPACE}" -o json | python3 -c '
import json, sys
for a in json.load(sys.stdin).get("actors", []):
    name = a["metadata"]["name"]
    if not name.startswith("ci-runner-"):
        continue
    s = a.get("status", {})
    w = s.get("workerAssignment", {})
    if w.get("workerPool") == "ci-runner":
        print(name, s.get("state", "-"), w.get("workerPool", "-"), s.get("assignedNode", "-"))
        break
'
}
if [[ "$(burst_replicas)" != 0 ]]; then
  echo "the burst WorkerPool has $(burst_replicas) replicas for one actor, want 0" >&2
  exit 1
fi
# The base worker holds two actors, so a third warm actor needs a burst
# worker. A short idle timeout lets all three suspend soon after.
kubectl -n ci-substrate set env deployment/ci-substrate-pool-tenant-a WARM=3 IDLE_AFTER=20s
kubectl -n ci-substrate rollout status deployment/ci-substrate-pool-tenant-a --timeout=180s
await_burst 1 120
echo "burst WorkerPool scaled to 1"
placement=""
deadline=$((SECONDS + 600))
while ((SECONDS < deadline)); do
  placement="$(burst_actor_placement)"
  if [[ -n "${placement}" ]]; then
    break
  fi
  sleep 5
done
if [[ -z "${placement}" ]]; then
  echo "no ci-runner-* actor ran on the burst WorkerPool" >&2
  kubectl ate get actors -a "${ATESPACE}" >&2 || true
  kubectl -n ci-substrate-workers get pods -o wide >&2
  kubectl -n ci-substrate logs deployment/ci-substrate-pool-tenant-a --tail=40 >&2
  exit 1
fi
actor="${placement%% *}"
node="${placement##* }"
if [[ "$(kubectl get node "${node}" -o jsonpath='{.metadata.labels.ci-substrate\.imjasonh\.com/burst}')" != "true" ]]; then
  echo "${actor} ran on ${node}, which is not a burst node" >&2
  exit 1
fi
echo "${actor} ran on burst node ${node}"
await_burst 0 300
echo "burst WorkerPool scaled to 0"
kubectl ate get actors -a "${ATESPACE}"
kubectl -n ci-substrate set env deployment/ci-substrate-pool-tenant-a WARM=1 IDLE_AFTER=2m
kubectl -n ci-substrate rollout status deployment/ci-substrate-pool-tenant-a --timeout=180s
