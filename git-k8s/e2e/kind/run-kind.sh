#!/usr/bin/env bash
# Install git-k8s and its checks in a kind cluster with kube's generate
# command, which pushes their images to a local registry, then push
# branches to a git server and check that they're fixed, gated, and
# landed. go test ./e2e/kind runs this when GIT_K8S_KIND_E2E=1,
# which CI sets when git-k8s changes.
#
# The git server runs on this machine and requires a password. Pods reach it
# through the kind network's gateway, so the nodes need no internet access.
# It plays the external repository: only the mirror in the core program
# reaches it, and the checks and test Pods fetch and push through the
# mirror. The script reaches the mirror through kubectl port-forward, with
# service account tokens for the mirror's audience.
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
PORT_FORWARD_PID=""

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
  k -n "${NS}" get pods,networkpolicies -o wide || true
  k -n "${NS}" logs --all-containers --prefix --tail=50 -l app.kubernetes.io/name=check-gotest || true
  for program in git-k8s "${CHECKS[@]}"; do
    k -n "${program}" describe pods || true
    k -n "${program}" logs --all-containers --prefix --tail=200 -l "app.kubernetes.io/name=${program}" || true
  done
  echo "--- git server log"
  cat "${WORKDIR}/gitserver.log" || true
  echo "--- port-forward log"
  cat "${WORKDIR}/port-forward.log" || true
  echo "::endgroup::"
}

finish() {
  local status=$?
  if [[ ${status} -ne 0 ]]; then
    diagnose
  fi
  if [[ -n "${PORT_FORWARD_PID}" ]]; then
    kill "${PORT_FORWARD_PID}" 2>/dev/null || true
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
need timeout
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
  -kube-context="${CONTEXT}" >"${WORKDIR}/gitserver.log" 2>&1 &
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
# git-k8s installs the CustomResourceDefinitions that the checks watch. The
# service account e2e-deps stands in for a controller that starts branches.
install git-k8s -- "-branch-prefix=${NS}/e2e-deps=deps/" "-fake-github=${CLUSTER_URL}/github"
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
# The gotest check runs Pods only in namespaces that opt in and enforce Pod
# Security.
k label namespace "${NS}" git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
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
    - match: deps/**
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

echo "::group::The API server rejects a URL that git could read as an option"
url_repository() {
  cat <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: url-check
  namespace: ${NS}
spec:
  url: '$1'
EOF
}
for url in '--upload-pack=touch /tmp/pwned' 'ssh://%2doProxyCommand=touch/app.git' \
  'ssh://[-oProxyCommand=touch]/app.git' 'ssh://[-oProxyCommand=touch]@example.com/app.git'; do
  if url_repository "${url}" | k apply --dry-run=server -f - 2>"${WORKDIR}/apply.err"; then
    echo "the API server accepted ${url}" >&2
    exit 1
  fi
  cat "${WORKDIR}/apply.err"
  grep -q 'spec.url' "${WORKDIR}/apply.err"
done
url_repository "git@[${GATEWAY}:2222]:app.git" | k apply --dry-run=server -f -
echo "The API server rejected URLs that git could read as options and accepted an scp-like address."
echo "::endgroup::"

# forward_mirror port-forwards a local port to the core program's Service,
# which serves the mirror, and sets MIRROR to the base URL of NS's copies.
# A port-forward goes to one Pod, so it needs restarting with the Pod.
forward_mirror() {
  if [[ -n "${PORT_FORWARD_PID}" ]]; then
    kill "${PORT_FORWARD_PID}" 2>/dev/null || true
    wait "${PORT_FORWARD_PID}" 2>/dev/null || true
  fi
  k -n git-k8s port-forward service/git-k8s :80 >"${WORKDIR}/port-forward.log" 2>&1 &
  PORT_FORWARD_PID=$!
  forwarding() { grep -qE '^Forwarding from 127[.]0[.]0[.]1:[0-9]+' "${WORKDIR}/port-forward.log"; }
  eventually 30 forwarding
  MIRROR="http://127.0.0.1:$(grep -oE '127[.]0[.]0[.]1:[0-9]+' "${WORKDIR}/port-forward.log" | head -n 1 | cut -d: -f2)/${NS}"
}
# mirror_token prints a token for the mirror for service account $2 in
# namespace $1.
mirror_token() { k -n "$1" create token "$2" --audience=git-k8s-mirror; }
# mg runs git in the working repository with token $1 for the mirror.
mg() {
  local token=$1
  shift
  g -c "http.extraHeader=Authorization: Bearer ${token}" "$@"
}
forward_mirror
k -n "${NS}" create serviceaccount e2e-deps
DEPS_TOKEN="$(mirror_token "${NS}" e2e-deps)"
GOFMT_TOKEN="$(mirror_token check-gofmt check-gofmt)"

# remote_head prints a branch's commit in repository $2, or app, in the
# external repository.
remote_head() { g ls-remote "${HOST_URL}/${2:-app}.git" "refs/heads/$1" | cut -f1; }
# mirror_head prints a ref's commit in the mirror's copy of app.
mirror_head() { mg "${DEPS_TOKEN}" ls-remote "${MIRROR}/app.git" "$1" | cut -f1; }
# synced_condition prints a field of app's ExternalSynced condition, which
# says whether the external repository has every change in the mirror.
synced_condition() {
  k -n "${NS}" get gitrepository app -o jsonpath="{.status.conditions[?(@.type==\"ExternalSynced\")].$1}"
}
in_sync() { [[ "$(synced_condition reason)" == InSync ]]; }
# branch_object prints the GitBranch for a branch of repository $2, or app.
branch_object() {
  k -n "${NS}" get gitbranches -l "git-k8s.imjasonh.com/repository=${2:-app}" \
    -o jsonpath="{.items[?(@.spec.branch==\"$1\")].metadata.name}"
}
fetch_main() { g fetch -q "${HOST_URL}/app.git" main; }
# A failed ls-remote prints nothing too, so it must not count as gone.
branch_gone() {
  local head
  head="$(remote_head "$1")" && [[ -z "${head}" && -z "$(branch_object "$1")" ]]
}

echo "::group::Only git-k8s's programs reach the mirror"
info_refs() {
  curl -sS -o "${WORKDIR}/mirror.txt" -w '%{http_code}' "$@" "${MIRROR}/app.git/info/refs?service=git-upload-pack"
}
[[ "$(info_refs)" == 401 ]]
[[ "$(info_refs -H "Authorization: Bearer $(k -n check-gofmt create token check-gofmt)")" == 401 ]]
cat "${WORKDIR}/mirror.txt"
k -n "${NS}" create serviceaccount stranger
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token "${NS}" stranger)")" == 404 ]]
cat "${WORKDIR}/mirror.txt"
[[ "$(info_refs -H "Authorization: Bearer ${GOFMT_TOKEN}")" == 200 ]]
[[ -n "$(mirror_head refs/heads/main)" && "$(mirror_head refs/heads/main)" == "$(remote_head main)" ]]
for program in check-base check-gofmt check-risk check-approval check-gotest; do
  as="system:serviceaccount:${program}:${program}"
  if k auth can-i get secrets -n "${NS}" --as="${as}"; then
    echo "${program} can read Secrets" >&2
    exit 1
  fi
  if k -n "${program}" auth can-i create "serviceaccounts/${program}" --subresource=token --as="${as}"; then
    echo "${program} can create tokens for its service account" >&2
    exit 1
  fi
done
k -n git-k8s auth can-i create serviceaccounts/git-k8s --subresource=token --as=system:serviceaccount:git-k8s:git-k8s
echo "Without a token, or with one for the API server, the mirror answers 401, and to a service account that isn't a check or a controller, 404. No check can read Secrets or create tokens, and only the core program can create tokens for Octo STS."
echo "::endgroup::"

echo "::group::A check can't push to a parent through the mirror"
fetch_main
g checkout -q -B to-main FETCH_HEAD
echo main >"${WORK}/main.txt"
g add -A
g commit -qm "Push to main from a check"
if out="$(mg "${GOFMT_TOKEN}" push "${MIRROR}/app.git" HEAD:main 2>&1)"; then
  echo "the mirror took a check's push to main: ${out}" >&2
  exit 1
fi
echo "${out}"
grep -q 'main is a parent branch, which only the merge controller updates' <<<"${out}"
[[ "$(mirror_head refs/heads/main)" == "$(remote_head main)" ]]
g checkout -q main
echo "The mirror refused check-gofmt's push to main, with a reason that git showed."
echo "::endgroup::"

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
# grep -q would exit at the first match and fail the pipeline with SIGPIPE.
g log -1 --format=%B FETCH_HEAD | grep -x 'Git-K8s-Fixer: gofmt' >/dev/null
eventually 60 branch_gone c/fmt
g log --oneline FETCH_HEAD
k -n git-k8s logs deployment/git-k8s >"${WORKDIR}/core.log"
grep -q 'served a push.*caller=check-gofmt/check-gofmt' "${WORKDIR}/core.log"
eventually 60 in_sync
[[ "$(mirror_head refs/heads/main)" == "$(remote_head main)" ]]
echo "The gofmt check pushed a fix to the mirror, main fast-forwarded to it in the mirror, the mirror synced main to the git server, and c/fmt was deleted."
echo "::endgroup::"

echo "::group::The fix, the landing, and the deletion are events"
# has_event succeeds when controller $1 recorded an event with reason $2 and
# message $3, and prints the message.
has_event() {
  k -n "${NS}" get events --field-selector "reportingComponent=$1,reason=$2" \
    -o jsonpath='{range .items[*]}{.message}{"\n"}{end}' | grep -Fx -- "$3"
}
fmt_fix="$(g rev-parse FETCH_HEAD)"
fmt_from="$(g rev-parse FETCH_HEAD~2)"
eventually 30 has_event check-gofmt PushedFix "pushed ${fmt_fix:0:12} to c/fmt: 1 of 2 Go files need gofmt: util/add.go"
eventually 30 has_event merge Landed "fast-forwarded main from ${fmt_from:0:12} to c/fmt at ${fmt_fix:0:12}"
eventually 30 has_event merge DeletedBranch "deleted c/fmt at ${fmt_fix:0:12} after it landed on main"
k -n "${NS}" get events --sort-by=.metadata.creationTimestamp
echo "kubectl get events lists the gofmt check's fix and the merge controller's landing and deletion of c/fmt."
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
k -n "${NS}" create role approver --verb=get,list,watch,patch,approve --resource=gitbranches.git-k8s.imjasonh.com
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
rejected "set ${APPROVE} when you set ${APPROVED_BY}" annotate --as=alice "${APPROVED_BY}=alice"
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
rejected "${APPROVED_BY} can change by itself only when you take over an approval" annotate --as=alice "${APPROVED_BY}-"
echo "The policy rejected bad approvals, and c/auth waited through ${admin}'s."
echo "::endgroup::"

echo "::group::A MutatingAdmissionPolicy sets approved-by"
k apply -f "${ROOT}/config/approved-by.yaml"
approved_by_after() {
  annotate "$@" -o jsonpath='{.metadata.annotations.git-k8s\.imjasonh\.com/approved-by}'
}
# Without the mutating policy, removing approve alone is rejected.
mutating_policy_ready() { approved_by_after "${APPROVE}-" --dry-run=server >/dev/null 2>&1; }
eventually 60 mutating_policy_ready
revoked="$(approved_by_after "${APPROVE}-")"
# The mutating policy keeps an approved-by that the request changes.
rejected "set ${APPROVED_BY} to alice" annotate --as=alice "${APPROVE}=${AUTH}" "${APPROVED_BY}=bob"
approved="$(approved_by_after "${APPROVE}=${AUTH}")"
echo "approved-by was '${revoked}' after ${admin} removed approve, and '${approved}' after they set it"
[[ -z "${revoked}" && "${approved}" == "${admin}" ]]
echo "${admin} removed and set approve alone, and the policy did the same to approved-by."
echo "::endgroup::"

echo "::group::Another approver can take over an approval"
# Admission sees only the object that a request produces, so setting approve
# to the commit that it already names changes nothing.
unchanged="$(approved_by_after --as=alice "${APPROVE}=${AUTH}" --dry-run=server)"
echo "approved-by is '${unchanged}' after alice set approve to the commit that it names"
[[ "${unchanged}" == "${admin}" ]]
rejected "requires the approve verb on gitbranches, which bob doesn't have" \
  annotate --as=bob "${APPROVE}=${AUTH}" "${APPROVED_BY}=bob"
rejected "take over an approval by setting it to alice" annotate --as=alice "${APPROVED_BY}=bob"
[[ "$(remote_head main)" == "${main_before}" ]]
annotate --as=alice "${APPROVE}=${AUTH}" "${APPROVED_BY}=alice"
auth_landed() { [[ "$(remote_head main)" == "${AUTH}" ]]; }
eventually 120 auth_landed
eventually 60 branch_gone c/auth
echo "bob couldn't take over ${admin}'s approval, and alice could, so the gate passed and c/auth landed."
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
g log --format=%B FETCH_HEAD | grep -x 'Git-K8s-Fixer: base' >/dev/null
g log --graph --oneline FETCH_HEAD
echo "One branch landed, the base check merged main into the other, and it landed too."
echo "::endgroup::"

# landing sets how branches land on main.
landing() {
  k -n "${NS}" patch gitrepository app --type=json \
    -p "[{\"op\":\"add\",\"path\":\"/spec/branches/0/merge/landing\",\"value\":\"$1\"}]"
}

echo "::group::A squash landing lands one commit"
landing Squash
fetch_main
squash_base="$(g rev-parse FETCH_HEAD)"
g checkout -q -B c/squash FETCH_HEAD
echo squash >"${WORK}/squash.txt"
g add -A
g commit -qm "Add squash.txt"
printf 'package util\nfunc  Sub(a,b int)int{return a-b}\n' >"${WORK}/util/sub.go"
g add -A
g commit -qm "Add util.Sub"
g push -q "${HOST_URL}/app.git" HEAD:c/squash
squash_landed() { branch_gone c/squash && fetch_main && g cat-file -e FETCH_HEAD:util/sub.go; }
eventually 180 squash_landed
g log --first-parent --format='%h %s (%an, committed by %cn)' "${squash_base}^..FETCH_HEAD"
[[ "$(g rev-list --count "${squash_base}..FETCH_HEAD")" == 1 ]]
[[ "$(g rev-parse FETCH_HEAD^)" == "${squash_base}" ]]
[[ "$(g log -1 --format='%an %cn' FETCH_HEAD)" == "e2e git-k8s" ]]
[[ "$(g log -1 --format=%B FETCH_HEAD)" == "Add squash.txt

* Add squash.txt
* Add util.Sub
* Format Go files with gofmt" ]]
[[ "$(g show FETCH_HEAD:util/sub.go)" == "package util

func Sub(a, b int) int { return a - b }" ]]
echo "The gofmt check fixed c/squash, and main moved by one squashed commit without the fixer trailer."
echo "::endgroup::"

echo "::group::A rebase landing copies a branch's commits onto its parent"
landing Rebase
fetch_main
g checkout -q -B c/rebase FETCH_HEAD
echo one >"${WORK}/rebase-one.txt"
g add -A
g commit -qm "Add rebase-one.txt"
echo two >"${WORK}/rebase-two.txt"
g add -A
g commit -qm "Add rebase-two.txt"
g checkout -q -B moves FETCH_HEAD
echo main >"${WORK}/main.txt"
g add -A
g commit -qm "Add main.txt"
rebase_base="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:main
g push -q "${HOST_URL}/app.git" c/rebase:c/rebase
rebase_landed() { branch_gone c/rebase && fetch_main && g cat-file -e FETCH_HEAD:rebase-two.txt; }
eventually 180 rebase_landed
g log --graph --format='%h %s (%an, committed by %cn)' "${rebase_base}^..FETCH_HEAD"
[[ "$(g log --reverse --format=%s "${rebase_base}..FETCH_HEAD")" == "Add rebase-one.txt
Add rebase-two.txt" ]]
[[ "$(g rev-list --parents "${rebase_base}..FETCH_HEAD" | awk 'NF != 2')" == "" ]]
[[ "$(g log --format='%an %cn' "${rebase_base}..FETCH_HEAD" | sort -u)" == "e2e git-k8s" ]]
g cat-file -e FETCH_HEAD:main.txt
echo "The base check merged main into c/rebase, and main moved by copies of its two commits, without the merge."
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
# check-gotest owns Pods, so generate lets it patch GitBranch objects, and
# only the policies stop it. Even a controller with the approve verb that
# names itself in approved-by can't approve.
k create clusterrole git-k8s-e2e-approve --verb=approve --resource=gitbranches.git-k8s.imjasonh.com
k create clusterrolebinding git-k8s-e2e-approve --clusterrole=git-k8s-e2e-approve \
  --serviceaccount=check-gotest:check-gotest --serviceaccount=git-k8s:git-k8s
controllers_can_approve() {
  for sa in check-gotest git-k8s; do
    k -n "${NS}" auth can-i approve gitbranches.git-k8s.imjasonh.com --as="system:serviceaccount:${sa}:${sa}" >/dev/null || return 1
  done
}
eventually 30 controllers_can_approve
# cant_approve passes if the API server rejects the service account $1's
# patch $2 because controllers can't approve.
cant_approve() {
  local code
  code="$(patch_branch "$(k -n "$1" create token "$1")" "$2")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]] && grep -q "git-k8s controllers can't approve branches" "${WORKDIR}/patch.json"
}
for sa in check-gotest git-k8s; do
  cant_approve "${sa}" "{\"metadata\":{\"annotations\":{\"${APPROVE}\":\"0000000\",\"${APPROVED_BY}\":\"system:serviceaccount:${sa}:${sa}\"}}}"
done
# git-k8s-approvals lets anyone with the approve verb take over an approval,
# so on an approved branch only git-k8s-branches stops a controller that
# names itself in approved-by.
annotate_main() { k -n "${NS}" annotate --overwrite gitbranch "$(branch_object main)" "$@"; }
annotate_main "${APPROVE}=$(remote_head main)" "${APPROVED_BY}=${admin}"
for sa in check-gotest git-k8s; do
  cant_approve "${sa}" "{\"metadata\":{\"annotations\":{\"${APPROVED_BY}\":\"system:serviceaccount:${sa}:${sa}\"}}}"
done
annotate_main "${APPROVE}-" "${APPROVED_BY}-"
gotest_token="$(k -n check-gotest create token check-gotest)"
code="$(patch_branch "${gotest_token}" '{"metadata":{"labels":{"e2e":"changed"}}}')"
[[ "${code}" == 422 ]]
grep -q "the gotest check can't change GitBranch objects" "${WORKDIR}/patch.json"
# check-gofmt owns nothing, so generate doesn't let it patch GitBranch
# objects at all.
approve='{"metadata":{"annotations":{"git-k8s.imjasonh.com/approve":"0000000"}}}'
code="$(patch_branch "${token}" "${approve}")"
cat "${WORKDIR}/patch.json"
echo
[[ "${code}" == 403 ]]
grep -q 'cannot patch resource' "${WORKDIR}/patch.json"
echo "Neither a check nor the core controller can approve a branch or take over its approval, a check can't change one, and check-gofmt can't patch one."
echo "::endgroup::"

echo "::group::A branch that changes on both sides diverges until a commit has both heads"
fetch_main
g checkout -q -B deps/x FETCH_HEAD
echo base >"${WORK}/deps.txt"
g add -A
g commit -qm "Start deps/x"
DEPS_BASE="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:deps/x
in_mirror() { [[ "$(mirror_head "$1")" == "$2" ]]; }
eventually 60 in_mirror refs/heads/deps/x "${DEPS_BASE}"
eventually 60 in_sync
echo "A push to the git server reached the mirror."

# A wrong password keeps the mirror from reaching the git server while both
# sides change.
k -n "${NS}" patch secret app-creds --type=merge -p '{"stringData":{"password":"wrong"}}'
sync_failed() { [[ "$(synced_condition reason)" == SyncFailed ]]; }
eventually 90 sync_failed
synced_condition message
echo
g checkout -q -B in-mirror "${DEPS_BASE}"
echo mirror >"${WORK}/deps.txt"
g commit -qam "Change deps/x in the mirror"
IN_MIRROR="$(g rev-parse HEAD)"
mg "${DEPS_TOKEN}" push -q "${MIRROR}/app.git" HEAD:deps/x
g checkout -q -B in-external "${DEPS_BASE}"
echo external >"${WORK}/deps.txt"
g commit -qam "Change deps/x in the git server"
IN_EXTERNAL="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:deps/x
k -n "${NS}" patch secret app-creds --type=merge -p "{\"stringData\":{\"password\":\"${PASSWORD}\"}}"

diverged() { k -n "${NS}" get gitbranch "$(branch_object deps/x)" -o jsonpath="{.status.diverged.$1}"; }
DOWNSTREAM=refs/git-k8s/downstream/heads/deps/x
recorded() {
  [[ "$(diverged commit)" == "${IN_EXTERNAL}" && "$(diverged ref)" == "${DOWNSTREAM}" &&
    "$(synced_condition reason)" == Diverged ]]
}
eventually 120 recorded
synced_condition message
echo
[[ "$(mirror_head refs/heads/deps/x)" == "${IN_MIRROR}" && "$(remote_head deps/x)" == "${IN_EXTERNAL}" ]]
[[ "$(mirror_head "${DOWNSTREAM}")" == "${IN_EXTERNAL}" ]]
echo "Neither side was overwritten, and the mirror keeps the git server's head at ${DOWNSTREAM}."

k -n git-k8s rollout restart deployment/git-k8s
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
forward_mirror
eventually 60 recorded
[[ "$(mirror_head refs/heads/deps/x)" == "${IN_MIRROR}" && "$(mirror_head "${DOWNSTREAM}")" == "${IN_EXTERNAL}" ]]
echo "After the core program restarted, its volume still held both heads, and the divergence stayed recorded."

g checkout -q -B resolved "${IN_MIRROR}"
g merge -q --no-edit -s ours "${IN_EXTERNAL}"
RESOLVED="$(g rev-parse HEAD)"
mg "${DEPS_TOKEN}" push -q --force-with-lease="refs/heads/deps/x:${IN_MIRROR}" "${MIRROR}/app.git" HEAD:deps/x
resolved() { [[ "$(remote_head deps/x)" == "${RESOLVED}" && -z "$(diverged commit)" ]] && in_sync; }
eventually 120 resolved
echo "A commit with both heads cleared the divergence, and the mirror fast-forwarded the git server to it."
echo "::endgroup::"

echo "::group::A GitHub repository uses Octo STS tokens and gets check runs"
# The git server fakes GitHub and Octo STS under /github. Its token exchange
# has the API server review each token, because Octo STS can't reach a kind
# cluster's issuer.
GITHUB_URL="${HOST_URL}/github"
OCTO="${WORKDIR}/octo"
git init -q -b main "${OCTO}"
o() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${OCTO}" \
    -c user.name=e2e -c user.email=e2e@example.com "$@"
}
issuer="$(k get --raw /.well-known/openid-configuration | sed -nE 's/.*"issuer":"([^"]*)".*/\1/p')"
mkdir -p "${OCTO}/.github/chainguard"
# The fake reads trust policies as JSON, which is also YAML. Only the core
# program exchanges tokens: the mirror for gitIdentity, and the check-runs
# controller for checkRunsIdentity.
cat >"${OCTO}/.github/chainguard/git-k8s.sts.yaml" <<EOF
{
  "issuer": "${issuer}",
  "subject": "system:serviceaccount:git-k8s:git-k8s",
  "audience": "octo-sts.dev/${NS}",
  "permissions": {"contents": "write"}
}
EOF
cat >"${OCTO}/.github/chainguard/git-k8s-checks.sts.yaml" <<EOF
{
  "issuer": "${issuer}",
  "subject": "system:serviceaccount:git-k8s:git-k8s",
  "audience": "octo-sts.dev/${NS}",
  "permissions": {"checks": "write"}
}
EOF
printf 'module example.com/octo\n\ngo 1.24\n' >"${OCTO}/go.mod"
printf 'package main\n\nfunc main() {}\n' >"${OCTO}/main.go"
o add -A
o commit -qm "Initial commit"
o push -q "${GITHUB_URL}/acme/octo.git" HEAD:main
# The GitBranch for c/fmt stays after the branch lands, without
# deleteMergedBranches, so the check runs can be checked afterward.
octo_repository() {
  k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: octo
  namespace: $1
spec:
  url: ${CLUSTER_URL}/github/acme/octo.git
  octoSTS:
    gitIdentity: git-k8s
    checkRunsIdentity: git-k8s-checks
  pollInterval: 2s
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: gofmt
            mayPush: true
    - match: c/**
      parent: main
EOF
}
octo_repository "${NS}"
# condition prints field $3 of condition $2 of the GitRepository octo in
# namespace $1.
condition() {
  k -n "$1" get gitrepository octo -o jsonpath="{.status.conditions[?(@.type==\"$2\")].$3}"
}
octo_ready() {
  [[ "$(condition "${NS}" Ready status)" == True && "$(condition "${NS}" CheckRunsTokenIssued status)" == True ]]
}
eventually 120 octo_ready

o checkout -q -b c/fmt
printf 'package main\nfunc  main() {}\n' >"${OCTO}/main.go"
o commit -qam "Unformat main.go"
unformatted="$(o rev-parse HEAD)"
o push -q "${GITHUB_URL}/acme/octo.git" HEAD:c/fmt
octo_head() { git ls-remote "${GITHUB_URL}/acme/octo.git" "refs/heads/$1" | cut -f1; }
fix_landed() {
  local main
  main="$(octo_head main)"
  [[ "${main}" != "$(o rev-parse main)" && "${main}" != "${unformatted}" && "${main}" == "$(octo_head c/fmt)" ]]
}
eventually 120 fix_landed
fix="$(octo_head main)"
# check_run prints the status and conclusion of check $2's check run on
# commit $1.
check_run() {
  curl -fsS "${GITHUB_URL}/api/v3/repos/acme/octo/commits/$1/check-runs?check_name=git-k8s/$2" |
    sed -nE 's/.*"status":"([a-z_]+)","conclusion":"([a-z_]*)".*/\1 \2/p'
}
check_runs_published() {
  [[ "$(check_run "${unformatted}" gofmt)" == "completed neutral" &&
    "$(check_run "${fix}" gofmt)" == "completed success" &&
    "$(check_run "${fix}" base)" == "completed success" ]]
}
eventually 60 check_runs_published
echo "check-gofmt pushed a fix to the mirror, git-k8s landed it and pushed it to GitHub with Octo STS tokens, and the results became check runs."

k create namespace "${NS}-other"
octo_repository "${NS}-other"
refused() {
  [[ "$(condition "${NS}-other" Ready reason)" == CredentialsUnavailable &&
    "$(condition "${NS}-other" Ready message)" == *"audience \"octo-sts.dev/${NS}\" did not match"* ]]
}
eventually 60 refused
condition "${NS}-other" Ready message
echo
k delete namespace "${NS}-other" --wait=false
echo "A GitRepository in another namespace can't use the trust policies, whose audience names ${NS}."
echo "::endgroup::"

echo "::group::Tests run in a sandboxed Pod"
# kindnet, kind's network plugin, enforces NetworkPolicies only where the
# kernel has nfnetlink_queue. To find out, a Pod that a policy denies all
# egress tries to reach the git server until it can't. The plugin can take a
# few seconds to apply the policy to a new Pod, so the test decides that the
# cluster doesn't enforce NetworkPolicies only if the Pod still reaches the
# git server after 30 seconds. The test's own Pods, like check-gotest's,
# meet the restricted Pod Security Standard, so they start in a namespace
# that enforces it.
k apply -f - <<EOF
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: no-egress
  namespace: ${NS}
spec:
  podSelector:
    matchLabels:
      e2e: no-egress
  policyTypes: [Egress]
---
apiVersion: v1
kind: Pod
metadata:
  name: no-egress
  namespace: ${NS}
  labels:
    e2e: no-egress
spec:
  restartPolicy: Never
  automountServiceAccountToken: false
  securityContext: {runAsNonRoot: true, runAsUser: 65532, seccompProfile: {type: RuntimeDefault}}
  containers:
    - name: probe
      image: ${GIT_IMAGE}
      command: [dash, -c, "read -r _"]
      stdin: true
      securityContext: {allowPrivilegeEscalation: false, capabilities: {drop: [ALL]}}
      env:
        - {name: HOME, value: /tmp}
        - {name: GIT_TERMINAL_PROMPT, value: "0"}
        - {name: GIT_ALLOW_PROTOCOL, value: "http:https:git:ssh"}
EOF
k -n "${NS}" wait --for=condition=Ready pod/no-egress --timeout=120s
no_egress() {
  ! timeout 20 kubectl --context "${CONTEXT}" -n "${NS}" exec no-egress -- \
    git ls-remote --end-of-options "http://git-k8s:${PASSWORD}@${GATEWAY}:${GIT_PORT}/app.git" >/dev/null 2>&1
}
ENFORCED=1
if ! eventually 30 no_egress 2>/dev/null; then
  ENFORCED=0
  echo "This cluster doesn't enforce NetworkPolicies, so the test doesn't check what test Pods can reach."
fi
k -n "${NS}" delete pod/no-egress networkpolicy/no-egress --wait=false

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
if [[ ${ENFORCED} -eq 1 ]]; then
  # The test Pods' NetworkPolicy lets them reach only the mirror and CoreDNS,
  # so this test passes only in a Pod that can't reach the git server,
  # CoreDNS's metrics port, or, if the node can reach the internet, a public
  # DNS server. kindnet doesn't filter a Pod's connections to its own node,
  # which on a one-node cluster include the API server.
  cat >"${TESTED}/sandbox_test.go" <<GO
package tested

import (
	"net"
	"testing"
	"time"
)

func TestSandbox(t *testing.T) {
	if _, err := net.LookupHost("kube-dns.kube-system.svc.cluster.local"); err != nil {
		t.Fatalf("looking up CoreDNS: %v", err)
	}
	for _, addr := range []string{"${GATEWAY}:${GIT_PORT}", "kube-dns.kube-system.svc.cluster.local:9153", "1.1.1.1:53"} {
		if c, err := net.DialTimeout("tcp", addr, 3*time.Second); err == nil {
			c.Close()
			t.Errorf("the test Pod reached %s", addr)
		}
	}
}
GO
fi
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
gotest c/broken message | grep -- '--- FAIL: TestAdd' >/dev/null
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
if [[ ${ENFORCED} -eq 1 ]]; then
  echo "The test Pods fetched from the mirror, and could resolve names but couldn't reach the git server, CoreDNS's metrics port, or a public DNS server."
else
  echo "The test Pods fetched from the mirror."
fi
# The core program owns a NetworkPolicy for each GitRepository that selects
# the Pods with check-gotest's controller label. The mirror lets only Pods
# with that label fetch, so the test Pods that fetched have it, even where
# the cluster doesn't enforce the policy.
selects_test_pods() {
  [[ "$(k -n "${NS}" get networkpolicy "$1-test-pods" --ignore-not-found \
    -o jsonpath='{.spec.podSelector.matchLabels.kube\.imjasonh\.github\.io/controller}')" == check-gotest ]]
}
selects_test_pods app
selects_test_pods tested
can_i() { k auth can-i "$1" networkpolicies -n "${NS}" --as="system:serviceaccount:$2:$2" || true; }
for verb in create patch delete; do
  [[ "$(can_i "${verb}" check-gotest)" == no && "$(can_i "${verb}" git-k8s)" == yes ]]
done
k -n "${NS}" delete networkpolicy tested-test-pods
tested_selects_test_pods() { selects_test_pods tested; }
eventually 60 tested_selects_test_pods
echo "Each GitRepository's NetworkPolicy selects check-gotest's Pods, check-gotest can't change NetworkPolicies, and the core program created a deleted policy again."
echo "::endgroup::"

echo "::group::The mirror checks a test Pod, not just its name"
# A person writes a gotest result that names a Pod, as only check-gotest's
# service account or a person can. The mirror lets a token that's bound to
# the Pod fetch only while the Pod has check-gotest's controller label,
# isn't being deleted, and is Pending, as check-gotest's Pods are while
# their init container fetches. gotest-named stays Pending because its init
# container waits. That container ignores SIGTERM, so a deleted Pod stays in
# its 30-second grace period, while the API server still accepts its token.
# gotest-running has no init container, so it runs.
k apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: gotest-named
  namespace: ${NS}
  labels:
    kube.imjasonh.github.io/controller: check-gotest
spec:
  restartPolicy: Never
  automountServiceAccountToken: false
  securityContext: {runAsNonRoot: true, runAsUser: 65532, seccompProfile: {type: RuntimeDefault}}
  initContainers:
    - name: fetch
      image: ${GIT_IMAGE}
      command: [dash, -c, "trap '' TERM; read -r _"]
      stdin: true
      securityContext: {allowPrivilegeEscalation: false, capabilities: {drop: [ALL]}}
  containers:
    - name: test
      image: ${GIT_IMAGE}
      command: [dash, -c, "read -r _"]
      stdin: true
      securityContext: {allowPrivilegeEscalation: false, capabilities: {drop: [ALL]}}
---
apiVersion: v1
kind: Pod
metadata:
  name: gotest-running
  namespace: ${NS}
  labels:
    kube.imjasonh.github.io/controller: check-gotest
spec:
  restartPolicy: Never
  automountServiceAccountToken: false
  securityContext: {runAsNonRoot: true, runAsUser: 65532, seccompProfile: {type: RuntimeDefault}}
  containers:
    - name: test
      image: ${GIT_IMAGE}
      command: [dash, -c, "read -r _"]
      stdin: true
      securityContext: {allowPrivilegeEscalation: false, capabilities: {drop: [ALL]}}
EOF
named_waits() {
  [[ -n "$(k -n "${NS}" get pod gotest-named -o jsonpath='{.status.initContainerStatuses[0].state.running.startedAt}')" ]]
}
eventually 120 named_waits
k -n "${NS}" wait --for=condition=Ready pod/gotest-running --timeout=120s
[[ "$(k -n "${NS}" get pod gotest-named -o jsonpath='{.status.phase}')" == Pending ]]
named_result() {
  k -n "${NS}" patch gitbranch "$(branch_object main)" --subresource=status --type=merge \
    -p '{"status":{"checks":{"gotest":{"commit":"0000000","state":"Running","outputs":{"pod":"'"$1"'"}}}}}' >/dev/null
}
# pod_token prints a token for the mirror that's bound to Pod $1.
pod_token() {
  k -n "${NS}" create token default --audience=git-k8s-mirror --bound-object-kind=Pod \
    --bound-object-name="$1" --bound-object-uid="$(k -n "${NS}" get pod "$1" -o jsonpath='{.metadata.uid}')"
}
named_result gotest-named
named_token="$(pod_token gotest-named)"
named_fetch() { info_refs -H "Authorization: Bearer ${named_token}"; }
named_fetches() { [[ "$(named_fetch)" == 200 ]]; }
eventually 30 named_fetches
k -n "${NS}" label pod gotest-named --overwrite kube.imjasonh.github.io/controller=check-other
[[ "$(named_fetch)" == 404 ]]
k -n "${NS}" label pod gotest-named kube.imjasonh.github.io/controller-
[[ "$(named_fetch)" == 404 ]]
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token "${NS}" default)")" == 404 ]]
k -n "${NS}" label pod gotest-named kube.imjasonh.github.io/controller=check-gotest
[[ "$(named_fetch)" == 200 ]]
# Once gotest-named can't fetch, the mirror has the result that names
# gotest-running, so the mirror refuses gotest-running only because it runs.
named_result gotest-running
named_refused() { [[ "$(named_fetch)" == 404 ]]; }
eventually 30 named_refused
[[ "$(info_refs -H "Authorization: Bearer $(pod_token gotest-running)")" == 404 ]]
named_result gotest-named
eventually 30 named_fetches
k -n "${NS}" delete pod gotest-named --wait=false
[[ "$(named_fetch)" == 404 ]]
k -n "${NS}" delete pod gotest-named gotest-running --grace-period=0 --force --ignore-not-found 2>/dev/null
k -n "${NS}" patch gitbranch "$(branch_object main)" --subresource=status --type=merge \
  -p '{"status":{"checks":{"gotest":null}}}' >/dev/null
echo "A Pending Pod that a gotest result names fetched with check-gotest's label, and not with another check's label, without the label, or while it was being deleted. A running Pod that the result named couldn't fetch, and neither could the same service account's token without a Pod."
echo "::endgroup::"

echo "::group::A check can change only its own Pods"
gotest_token="$(k -n check-gotest create token check-gotest)"
# pod_request sends request $1 for the Pods path $2 under
# /api/v1/namespaces/, with body $3, as check-gotest, without changing
# anything.
pod_request() {
  local type=application/json
  [[ "$1" == PATCH ]] && type=application/merge-patch+json
  curl -sS --cacert "${WORKDIR}/ca.crt" -o "${WORKDIR}/pod.json" -w '%{http_code}' -X "$1" \
    -H "Authorization: Bearer ${gotest_token}" -H "Content-Type: ${type}" \
    --data "${3:-}" "${server}/api/v1/namespaces/$2?dryRun=All"
}
# gotest_pod prints a Pod named $3, or gotest-e2e if $3 is empty, that meets
# the restricted Pod Security Standard, with the gotest check's label, that
# runs as service account $1 on node $2, or on the node that the scheduler
# picks if $2 is empty.
gotest_pod() {
  cat <<EOF
{"apiVersion": "v1", "kind": "Pod",
 "metadata": {"name": "${3:-gotest-e2e}", "labels": {"kube.imjasonh.github.io/controller": "check-gotest"}},
 "spec": {"serviceAccountName": "$1", "nodeName": "${2:-}", "restartPolicy": "Never", "automountServiceAccountToken": false,
  "securityContext": {"runAsNonRoot": true, "runAsUser": 65532, "seccompProfile": {"type": "RuntimeDefault"}},
  "containers": [{"name": "test", "image": "${GO_IMAGE}", "command": ["go", "version"],
   "securityContext": {"allowPrivilegeEscalation": false, "capabilities": {"drop": ["ALL"]}}}]}}
EOF
}
code="$(pod_request POST "${NS}/pods" "$(gotest_pod default)")"
[[ "${code}" == 201 ]]
code="$(pod_request POST check-gofmt/pods "$(gotest_pod check-gofmt)")"
cat "${WORKDIR}/pod.json"
echo
[[ "${code}" == 422 ]]
grep -q "the gotest check can't change Pods in the namespaces of git-k8s programs" "${WORKDIR}/pod.json"
code="$(pod_request POST "${NS}/pods" "$(gotest_pod rogue)")"
[[ "${code}" == 422 ]]
grep -q "the gotest check's Pods must run as their namespace's default service account" "${WORKDIR}/pod.json"
code="$(pod_request POST default/pods "$(gotest_pod default)")"
[[ "${code}" == 422 ]]
grep -q "can't create or change Pods in namespace default, which doesn't have the label git-k8s.imjasonh.com/check-pods=true" "${WORKDIR}/pod.json"
code="$(pod_request POST "${NS}/pods" "$(gotest_pod default "${CLUSTER}-control-plane")")"
[[ "${code}" == 422 ]]
grep -q "the gotest check can't assign its Pods to a node" "${WORKDIR}/pod.json"
code="$(pod_request POST "${NS}/pods" "$(gotest_pod default "" review-e2e)")"
[[ "${code}" == 422 ]]
grep -q "the gotest check's new Pods need a name of the form gotest-ID, where ID has no hyphens" "${WORKDIR}/pod.json"
k -n "${NS}" apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: other
spec:
  restartPolicy: Never
  automountServiceAccountToken: false
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: other
      image: ${GO_IMAGE}
      command: [go, version]
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
EOF
code="$(pod_request PATCH "${NS}/pods/other" '{"metadata":{"labels":{"kube.imjasonh.github.io/controller":"check-gotest"}}}')"
cat "${WORKDIR}/pod.json"
echo
[[ "${code}" == 422 ]]
grep -q "the gotest check can change or delete only its own Pods" "${WORKDIR}/pod.json"
code="$(pod_request DELETE "${NS}/pods/other")"
[[ "${code}" == 422 ]]
grep -q "the gotest check can change or delete only its own Pods" "${WORKDIR}/pod.json"
k -n "${NS}" delete pod other
echo "check-gotest can't run Pods in a program's namespace, as another service account, in a namespace that doesn't opt in, on a node that it names, or under another check's Pod name, and can't change or delete a Pod that it didn't create."
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
