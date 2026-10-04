#!/usr/bin/env bash
# Install git-k8s and its checks in a kind cluster with kube's generate
# command, which pushes their images to a local registry, then push
# branches to a git server and check that they're fixed, gated, and
# fast-forwarded. go test ./e2e/kind runs this when GIT_K8S_KIND_E2E=1,
# which CI sets when git-k8s changes.
#
# The git server runs on this machine and requires a password. Pods reach it
# through the kind network's gateway, so the nodes need no internet access.
#
# GIT_K8S_KIND_CHAINGUARD is where Chainguard's images come from
# (cgr.dev/chainguard; docker.io/chainguard is a mirror).
# GIT_K8S_KIND_KEEP=1 keeps the cluster, registry, and git server afterward.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CLUSTER="${GIT_K8S_KIND_CLUSTER:-git-k8s-e2e}"
CONTEXT="kind-${CLUSTER}"
REGISTRY="${GIT_K8S_KIND_REGISTRY:-git-k8s-e2e-registry}"
PORT="${GIT_K8S_KIND_REGISTRY_PORT:-5002}"
GIT_PORT="${GIT_K8S_KIND_GIT_PORT:-18418}"
CHAINGUARD="${GIT_K8S_KIND_CHAINGUARD:-cgr.dev/chainguard}"
PLATFORM="linux/$(go env GOARCH)"
NS=git-k8s-e2e
CHECKS=(check-base check-gofmt check-risk check-approval check-gotest)
WORKDIR="$(mktemp -d)"
WORK="${WORKDIR}/work"
PASSWORD="$(od -An -N12 -tx1 /dev/urandom | tr -d ' \n')"
CREATED_CLUSTER=0
CREATED_REGISTRY=0
GIT_SERVER_PID=""

k() { kubectl --context "${CONTEXT}" "$@"; }

# g runs git in the working repository, without the machine's git config.
g() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${WORK}" \
    -c user.name=e2e -c user.email=e2e@example.com "$@"
}

diagnose() {
  echo "::group::Cluster state"
  k get nodes -o wide || true
  k -n "${NS}" get gitrepositories,gitbranches -o yaml || true
  k -n "${NS}" get pods -o wide || true
  k -n "${NS}" logs --all-containers --prefix --tail=50 -l app.kubernetes.io/name=check-gotest || true
  for program in git-k8s "${CHECKS[@]}"; do
    k -n "${program}" describe pods || true
    k -n "${program}" logs --all-containers --prefix --tail=200 -l "app.kubernetes.io/name=${program}" || true
  done
  echo "--- git server log"
  cat "${WORKDIR}/gitserver.log" || true
  echo "::endgroup::"
}

finish() {
  local status=$?
  if [[ ${status} -ne 0 ]]; then
    diagnose
  fi
  if [[ "${GIT_K8S_KIND_KEEP:-}" == 1 ]]; then
    echo "Kept the cluster ${CLUSTER}, the registry ${REGISTRY}, and the git server in ${WORKDIR}"
    exit "${status}"
  fi
  if [[ -n "${GIT_SERVER_PID}" ]]; then
    kill "${GIT_SERVER_PID}" 2>/dev/null || true
  fi
  if [[ ${CREATED_CLUSTER} -eq 1 ]]; then
    kind delete cluster --name "${CLUSTER}" || true
  fi
  if [[ ${CREATED_REGISTRY} -eq 1 ]]; then
    docker rm -f "${REGISTRY}" >/dev/null || true
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
need git
need curl
install_kind
docker info >/dev/null

echo "::group::Start a registry, a kind cluster, and a git server"
# As in https://kind.sigs.k8s.io/docs/user/local-registry/: nodes pull
# localhost:PORT/... from the registry container, which is on kind's
# network.
if [[ "$(docker inspect -f '{{.State.Running}}' "${REGISTRY}" 2>/dev/null || true)" != true ]]; then
  docker run -d --restart=always -p "127.0.0.1:${PORT}:5000" --name "${REGISTRY}" registry:2
  CREATED_REGISTRY=1
fi
if ! kind get clusters 2>/dev/null | grep -x "${CLUSTER}" >/dev/null; then
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

# Pods reach the git server on this machine through the gateway of kind's
# Docker network.
GATEWAY="$(docker network inspect kind -f '{{range .IPAM.Config}}{{.Gateway}} {{end}}' | tr ' ' '\n' |
  grep -E '^[0-9]+[.][0-9]+[.][0-9]+[.][0-9]+$' | head -n 1)"
(cd "${ROOT}" && go build -o "${WORKDIR}/gitserver" ./e2e/gitserver)
mkdir -p "${WORKDIR}/repos"
GITSERVER_PASSWORD="${PASSWORD}" "${WORKDIR}/gitserver" -addr="0.0.0.0:${GIT_PORT}" -root="${WORKDIR}/repos" \
  >"${WORKDIR}/gitserver.log" 2>&1 &
GIT_SERVER_PID=$!
HOST_URL="http://git-k8s:${PASSWORD}@127.0.0.1:${GIT_PORT}"
CLUSTER_URL="http://${GATEWAY}:${GIT_PORT}"
listening() { (echo >"/dev/tcp/127.0.0.1/${GIT_PORT}") 2>/dev/null; }
eventually 30 listening
echo "Pods reach the git server at ${CLUSTER_URL}"
echo "::endgroup::"

echo "::group::Install git-k8s and the checks with generate"
cd "${ROOT}"
generate() {
  local program=$1
  shift
  go run "./cmd/${program}" generate -registry="localhost:${PORT}/git-k8s-e2e" \
    -base="${CHAINGUARD}/git:latest" -platform="${PLATFORM}" -replicas=1 "$@"
}
install() {
  generate "$@" | k apply -f -
}
# The gotest check's Pods use these images. Copying them into the local
# registry lets the nodes pull them without reaching the internet.
GO_IMAGE="localhost:${PORT}/chainguard/go:latest"
GIT_IMAGE="localhost:${PORT}/chainguard/git:latest"
crane() { go run github.com/google/go-containerregistry/cmd/crane@v0.22.1 "$@"; }
crane copy --platform "${PLATFORM}" "${CHAINGUARD}/go:latest" "${GO_IMAGE}"
crane copy --platform "${PLATFORM}" "${CHAINGUARD}/git:latest" "${GIT_IMAGE}"
# git-k8s installs the CustomResourceDefinitions that the checks watch.
install git-k8s
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
for program in "${CHECKS[@]}"; do
  case "${program}" in
    check-risk) install "${program}" -- '-sensitive=auth/**' ;;
    check-gotest)
      install "${program}" -- "-go-image=${GO_IMAGE}" "-git-image=${GIT_IMAGE}" -timeout=5m
      ;;
    *) install "${program}" ;;
  esac
done
for program in "${CHECKS[@]}"; do
  k -n "${program}" rollout status "deployment/${program}" --timeout=180s
done
k apply -f "${ROOT}/config/policy.yaml"
echo "::endgroup::"

echo "::group::Track a repository"
git init -q -b main "${WORK}"
printf 'module example.com/app\n\ngo 1.24\n' >"${WORK}/go.mod"
printf 'package main\n\nfunc main() {}\n' >"${WORK}/main.go"
g add -A
g commit -qm "Initial commit"
g push -q "${HOST_URL}/app.git" HEAD:main

k create namespace "${NS}"
k -n "${NS}" create secret generic app-creds --type=kubernetes.io/basic-auth \
  --from-literal=username=git-k8s --from-literal=password="${PASSWORD}"
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: app
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/app.git
  secretRef:
    name: app-creds
  pollInterval: 2s
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: gofmt
            mayPush: true
          - name: risk
          - name: approval
        when: >-
          checks.base.passed && checks.gofmt.passed &&
          (checks.risk.outputs.level == "low" ||
          (checks.approval.passed && checks.approval.outputs.approver == "alice"))
        deleteMergedBranches: true
    - match: c/**
      parent: main
EOF
repository_ready() {
  [[ "$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="Ready")].status}')" == True ]]
}
eventually 120 repository_ready
policies_installed() {
  [[ "$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="PoliciesInstalled")].status}')" == True ]]
}
eventually 60 policies_installed
k -n "${NS}" get gitrepositories,gitbranches
echo "::endgroup::"

# remote_head prints a branch's commit in repository $2, or app.
remote_head() { git ls-remote "${HOST_URL}/${2:-app}.git" "refs/heads/$1" | cut -f1; }
# branch_object prints the GitBranch for a branch of repository $2, or app.
branch_object() {
  k -n "${NS}" get gitbranches -l "git-k8s.imjasonh.com/repository=${2:-app}" \
    -o jsonpath="{.items[?(@.spec.branch==\"$1\")].metadata.name}"
}
fetch_main() { g fetch -q "${HOST_URL}/app.git" main; }
branch_gone() { [[ -z "$(remote_head "$1")" && -z "$(branch_object "$1")" ]]; }

echo "::group::A branch with unformatted Go lands formatted"
g checkout -q -b c/fmt
mkdir -p "${WORK}/util"
printf 'package util\nfunc  Add(a,b int)int{return a+b}\n' >"${WORK}/util/add.go"
g add -A
g commit -qm "Add util.Add"
g push -q "${HOST_URL}/app.git" HEAD:c/fmt
formatted='package util

func Add(a, b int) int { return a + b }'
formatted_on_main() { fetch_main && [[ "$(g show FETCH_HEAD:util/add.go 2>/dev/null)" == "${formatted}" ]]; }
eventually 120 formatted_on_main
g log -1 --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Fixer: gofmt'
eventually 60 branch_gone c/fmt
g log --oneline FETCH_HEAD
echo "The gofmt check pushed a fix, main fast-forwarded to it, and c/fmt was deleted."
echo "::endgroup::"

echo "::group::A risky branch waits for approval"
g checkout -q -B c/auth FETCH_HEAD
mkdir -p "${WORK}/auth"
printf 'package auth\n\n// Allow reports whether user can continue.\nfunc Allow(user string) bool { return user != "" }\n' \
  >"${WORK}/auth/policy.go"
g add -A
g commit -qm "Add auth.Allow"
AUTH="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:c/auth
field() { k -n "${NS}" get gitbranch "$(branch_object c/auth)" -o jsonpath="$1"; }
waiting_for_approval() {
  [[ -n "$(branch_object c/auth)" ]] &&
    [[ "$(field '{.status.state}')" == WaitingForChecks ]] &&
    [[ "$(field '{.status.checks.risk.outputs.level}')" == high ]] &&
    [[ "$(field '{.status.checks.approval.state}')" == Failed ]] &&
    [[ "$(field '{.status.checks.gofmt.state}')" == Passed ]]
}
eventually 120 waiting_for_approval
main_before="$(remote_head main)"
sleep 6
[[ "$(remote_head main)" == "${main_before}" ]]
field '{.status.conditions[?(@.type=="Merged")].message}'
echo
echo "c/auth waits for approval with a high risk rating."
echo "::endgroup::"

echo "::group::Approvals name the approver"
k -n "${NS}" create role approver --verb=get,patch,approve --resource=gitbranches.git-k8s.imjasonh.com
k -n "${NS}" create rolebinding alice --role=approver --user=alice
k -n "${NS}" create role editor --verb=get,patch --resource=gitbranches.git-k8s.imjasonh.com
k -n "${NS}" create rolebinding bob --role=editor --user=bob
roles_bound() {
  k -n "${NS}" auth can-i approve gitbranches.git-k8s.imjasonh.com --as=alice >/dev/null &&
    k -n "${NS}" auth can-i patch gitbranches.git-k8s.imjasonh.com --as=bob >/dev/null
}
eventually 30 roles_bound
APPROVE=git-k8s.imjasonh.com/approve
APPROVED_BY=git-k8s.imjasonh.com/approved-by
annotate() { k -n "${NS}" annotate --overwrite gitbranch "$(branch_object c/auth)" "$@"; }
# rejected passes if the API server rejects a server-side dry run of a
# command with a message that contains $1.
rejected() {
  local want=$1 status=0
  shift
  "$@" --dry-run=server >"${WORKDIR}/rejected.txt" 2>&1 || status=$?
  cat "${WORKDIR}/rejected.txt"
  [[ ${status} -ne 0 ]] && grep -qF -- "${want}" "${WORKDIR}/rejected.txt"
}
rejected "set ${APPROVED_BY} to alice" annotate --as=alice "${APPROVE}=${AUTH}"
rejected "set ${APPROVED_BY} to alice" annotate --as=alice "${APPROVE}=${AUTH}" "${APPROVED_BY}=bob"
rejected "requires the approve verb on gitbranches, which bob doesn't have" \
  annotate --as=bob "${APPROVE}=${AUTH}" "${APPROVED_BY}=bob"
rejected "${APPROVED_BY} can change only when ${APPROVE} does" annotate --as=alice "${APPROVED_BY}=alice"
# The gate wants alice's approval, so another approver's doesn't land c/auth.
admin="$(k auth whoami -o jsonpath='{.status.userInfo.username}')"
annotate "${APPROVE}=${AUTH}" "${APPROVED_BY}=${admin}"
approved_by() {
  [[ "$(field '{.status.checks.approval.state}')" == Passed ]] &&
    [[ "$(field '{.status.checks.approval.outputs.approver}')" == "$1" ]]
}
eventually 60 approved_by "${admin}"
gate_saw_approval() { field '{.status.conditions[?(@.type=="Merged")].message}' | grep -q 'approval Passed'; }
eventually 60 gate_saw_approval
[[ "$(field '{.status.state}')" == WaitingForChecks ]]
[[ "$(remote_head main)" == "${main_before}" ]]
rejected "remove ${APPROVED_BY} when you remove ${APPROVE}" annotate --as=alice "${APPROVE}-"
rejected "${APPROVED_BY} can change only when ${APPROVE} does" annotate --as=alice "${APPROVED_BY}-"
echo "The policy rejected bad approvals, and c/auth waited through ${admin}'s."
echo "::endgroup::"

echo "::group::A MutatingAdmissionPolicy sets approved-by"
k apply -f "${ROOT}/config/approved-by.yaml"
approved_by_annotation() {
  annotate --as=alice "$@" -o jsonpath='{.metadata.annotations.git-k8s\.imjasonh\.com/approved-by}'
}
# Without the mutating policy, removing approve alone is rejected.
mutating_policy_ready() { approved_by_annotation "${APPROVE}-" --dry-run=server >/dev/null 2>&1; }
eventually 60 mutating_policy_ready
revoked="$(approved_by_annotation "${APPROVE}-")"
# The mutating policy keeps an approved-by that the request sets.
rejected "set ${APPROVED_BY} to alice" annotate --as=alice "${APPROVE}=${AUTH}" "${APPROVED_BY}=bob"
approved="$(approved_by_annotation "${APPROVE}=${AUTH}")"
echo "approved-by was '${revoked}' after alice removed approve, and '${approved}' after she set it"
[[ -z "${revoked}" && "${approved}" == alice ]]
auth_landed() { [[ "$(remote_head main)" == "${AUTH}" ]]; }
eventually 120 auth_landed
eventually 60 branch_gone c/auth
echo "alice removed and set approve alone, the policy did the same to approved-by, and c/auth landed."
echo "::endgroup::"

echo "::group::Two branches from the same commit both land"
fetch_main
g checkout -q -B c/one FETCH_HEAD
echo one >"${WORK}/one.txt"
g add -A
g commit -qm "Add one.txt"
g checkout -q -B c/two FETCH_HEAD
echo two >"${WORK}/two.txt"
g add -A
g commit -qm "Add two.txt"
g push -q "${HOST_URL}/app.git" c/one:c/one c/two:c/two
both_landed() {
  branch_gone c/one && branch_gone c/two && fetch_main &&
    g cat-file -e FETCH_HEAD:one.txt && g cat-file -e FETCH_HEAD:two.txt
}
eventually 180 both_landed
g log --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Fixer: base'
g log --graph --oneline FETCH_HEAD
echo "One branch landed, the base check merged main into the other, and it landed too."
echo "::endgroup::"

echo "::group::A check can write only its own result"
server="$(k config view --minify -o jsonpath='{.clusters[0].cluster.server}')"
k config view --raw --minify -o jsonpath='{.clusters[0].cluster.certificate-authority-data}' |
  base64 -d >"${WORKDIR}/ca.crt"
token="$(k -n check-gofmt create token check-gofmt)"
status_url="${server}/apis/git-k8s.imjasonh.com/v1alpha1/namespaces/${NS}/gitbranches/$(branch_object main)/status?dryRun=All"
patch_status() {
  curl -sS --cacert "${WORKDIR}/ca.crt" -o "${WORKDIR}/patch.json" -w '%{http_code}' -X PATCH \
    -H "Authorization: Bearer ${2:-${token}}" -H 'Content-Type: application/merge-patch+json' \
    --data "$1" "${status_url}"
}
code="$(patch_status '{"status":{"checks":{"risk":{"commit":"0000000","state":"Passed"}}}}')"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 422 ]]
grep -q 'the gofmt check can only write status.checks.gofmt' "${WORKDIR}/patch.json"
code="$(patch_status '{"status":{"checks":{"gofmt":{"commit":"0000000","state":"Passed"}}}}')"
[[ "${code}" == 200 ]]
# A service account with check-gofmt's permissions but another name isn't a
# check, so it can't write any result.
k -n "${NS}" create serviceaccount rogue
k create clusterrolebinding git-k8s-e2e-rogue --clusterrole=check-gofmt --serviceaccount="${NS}:rogue"
rogue_token="$(k -n "${NS}" create token rogue)"
code="$(patch_status '{"status":{"checks":{"gofmt":{"commit":"0000000","state":"Passed"}}}}' "${rogue_token}")"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 422 ]]
grep -q "isn't a check's service account, so it can't write status.checks" "${WORKDIR}/patch.json"
echo "check-gofmt can write status.checks.gofmt but not status.checks.risk, and other service accounts can't write either."
echo "::endgroup::"

echo "::group::Controllers can't approve branches"
branch_url="${server}/apis/git-k8s.imjasonh.com/v1alpha1/namespaces/${NS}/gitbranches/$(branch_object main)?dryRun=All"
patch_branch() {
  curl -sS --cacert "${WORKDIR}/ca.crt" -o "${WORKDIR}/patch.json" -w '%{http_code}' -X PATCH \
    -H "Authorization: Bearer $1" -H 'Content-Type: application/merge-patch+json' \
    --data "$2" "${branch_url}"
}
# Even a controller with the approve verb that names itself in approved-by
# can't approve.
k create clusterrole git-k8s-e2e-approve --verb=approve --resource=gitbranches.git-k8s.imjasonh.com
k create clusterrolebinding git-k8s-e2e-approve --clusterrole=git-k8s-e2e-approve \
  --serviceaccount=check-gofmt:check-gofmt --serviceaccount=git-k8s:git-k8s
controllers_can_approve() {
  for sa in check-gofmt git-k8s; do
    k -n "${NS}" auth can-i approve gitbranches.git-k8s.imjasonh.com --as="system:serviceaccount:${sa}:${sa}" >/dev/null || return 1
  done
}
eventually 30 controllers_can_approve
for sa in check-gofmt git-k8s; do
  approve="{\"metadata\":{\"annotations\":{\"${APPROVE}\":\"0000000\",\"${APPROVED_BY}\":\"system:serviceaccount:${sa}:${sa}\"}}}"
  code="$(patch_branch "$(k -n "${sa}" create token "${sa}")" "${approve}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]]
  grep -q "git-k8s controllers can't approve branches" "${WORKDIR}/patch.json"
done
code="$(patch_branch "${token}" '{"metadata":{"labels":{"e2e":"changed"}}}')"
[[ "${code}" == 422 ]]
grep -q "the gofmt check can't change GitBranch objects" "${WORKDIR}/patch.json"
echo "Neither a check nor the core controller can approve a branch, and a check can't change one."
echo "::endgroup::"

echo "::group::Tests run in a sandboxed Pod"
TESTED="${WORKDIR}/tested"
git init -q -b main "${TESTED}"
t() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${TESTED}" \
    -c user.name=e2e -c user.email=e2e@example.com "$@"
}
printf 'module example.com/tested\n\ngo 1.24\n' >"${TESTED}/go.mod"
printf 'package tested\n\nfunc Add(a, b int) int { return a + b }\n' >"${TESTED}/add.go"
cat >"${TESTED}/add_test.go" <<'GO'
package tested

import "testing"

func TestAdd(t *testing.T) {
	if got := Add(2, 3); got != 5 {
		t.Errorf("Add(2, 3) = %d, want 5", got)
	}
}
GO
t add -A
t commit -qm "Add Add"
t push -q "${HOST_URL}/tested.git" HEAD:main
tested_main="$(t rev-parse HEAD)"
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: tested
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/tested.git
  secretRef:
    name: app-creds
  pollInterval: 2s
  branches:
    - match: main
      merge:
        checks:
          - name: gotest
        deleteMergedBranches: true
    - match: c/**
      parent: main
EOF

t checkout -q -b c/broken
printf 'package tested\n\nfunc Add(a, b int) int { return a - b }\n' >"${TESTED}/add.go"
t commit -qam "Break Add"
t push -q "${HOST_URL}/tested.git" HEAD:c/broken
gotest() { k -n "${NS}" get gitbranch "$(branch_object "$1" tested)" -o jsonpath="{.status.checks.gotest.$2}"; }
broken_failed() { [[ -n "$(branch_object c/broken tested)" && "$(gotest c/broken state)" == Failed ]]; }
eventually 300 broken_failed
gotest c/broken message
echo
gotest c/broken message | grep -q -- '--- FAIL: TestAdd'
[[ "$(remote_head main tested)" == "${tested_main}" ]]
# kube deletes a test Pod once the check stops declaring it.
no_test_pods() { [[ -z "$(k -n "${NS}" get pods -l app.kubernetes.io/name=check-gotest -o name)" ]]; }
eventually 60 no_test_pods

t checkout -q -b c/fixed main
printf 'package tested\n\n// Add returns the sum of a and b.\nfunc Add(a, b int) int { return a + b }\n' >"${TESTED}/add.go"
t commit -qam "Document Add"
fixed="$(t rev-parse HEAD)"
t push -q "${HOST_URL}/tested.git" HEAD:c/fixed
fixed_landed() { [[ "$(remote_head main tested)" == "${fixed}" ]]; }
eventually 300 fixed_landed
eventually 60 no_test_pods
echo "A branch that breaks a test failed in a sandboxed Pod, and a fixed branch landed."
echo "::endgroup::"

echo "::group::Nothing writes while nothing changes"
snapshot() {
  k -n "${NS}" get gitrepositories,gitbranches \
    -o jsonpath='{range .items[*]}{.kind}/{.metadata.name}={.metadata.resourceVersion} {end}'
}
idle() {
  local before after
  before="$(snapshot)"
  sleep 8
  after="$(snapshot)"
  echo "resource versions: ${after}"
  [[ "${before}" == "${after}" ]]
}
eventually 60 idle
echo "Four polls of the remote wrote nothing."
echo "::endgroup::"

echo "kind e2e passed"
