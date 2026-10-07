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
# and git-k8s-deps's update Pods reach it, and the checks, git-k8s-deps,
# and test Pods fetch and push through the mirror. The script reaches the
# mirror through kubectl port-forward, with service account tokens for the
# mirror's audience. Like a forge that requires signed commits, the git
# server rejects a push that adds a commit that isn't signed with its
# committer's key, so this test signs its own commits, and git-k8s signs the
# commits that it makes.
#
# The git server also serves a Go module proxy at /proxy/, without a
# password. A second module proxy on this machine serves the one module that
# the tested repository's branches depend on, as go-cache's upstream.
#
# GIT_K8S_KIND_CHAINGUARD is where Chainguard's images come from
# (cgr.dev/chainguard; docker.io/chainguard is a mirror).
# GIT_K8S_KIND_KEEP=1 keeps the cluster, registry, git server, and module
# proxy afterward.
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
# check-approval runs in another namespace, so the admission policies
# recognize it only through its entry in the git-k8s-checks ConfigMap.
APPROVAL_NS=checks
WORKDIR="$(mktemp -d)"
WORK="${WORKDIR}/work"
PASSWORD="$(od -An -N12 -tx1 /dev/urandom | tr -d ' \n')"
# IDENTITY is the checks' default -identity-email, the committer of their
# commits.
IDENTITY=git-k8s@users.noreply.github.com
ALLOWED_SIGNERS="${WORKDIR}/allowed_signers"
CREATED_CLUSTER=0
CREATED_REGISTRY=0
GIT_SERVER_PID=""
PORT_FORWARD_PID=""
MOD_PROXY_PID=""
PROBE_PID=""
KIND_PID=""
AGENT_IMAGE_PID=""
GO_IMAGE_PID=""
ZOMBIES_PID=""
# GENERATING has the PID of each pregenerate that the test hasn't waited for,
# and GENERATED the exit status of each that it has.
declare -A GENERATING=() GENERATED=()

k() { kubectl --context "${CONTEXT}" "$@"; }

# SIGN makes git sign this test's commits with the e2e key, and check
# signatures against the git server's allowed signers.
SIGN=(-c gpg.format=ssh -c "user.signingKey=${WORKDIR}/e2e-key" -c commit.gpgSign=true
  -c "gpg.ssh.allowedSignersFile=${ALLOWED_SIGNERS}")

# namespace_of prints the namespace of program $1.
namespace_of() {
  if [[ "$1" == check-approval ]]; then
    echo "${APPROVAL_NS}"
  else
    echo "$1"
  fi
}

# g runs git in the working repository, without the machine's git config.
g() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${WORK}" \
    -c user.name=e2e -c user.email=e2e@example.com "${SIGN[@]}" "$@"
}

diagnose() {
  echo "::group::Cluster state"
  k get nodes -o wide || true
  k -n "${NS}" get gitrepositories,gitbranches -o yaml || true
  k -n "${NS}" get pods,networkpolicies -o wide || true
  k -n "${NS}" logs --all-containers --prefix --tail=50 -l app.kubernetes.io/name=check-gotest || true
  k -n "${NS}" logs --all-containers --prefix --tail=50 -l app.kubernetes.io/name=git-k8s-agent || true
  k -n "${NS}" logs --all-containers --prefix --tail=50 -l app.kubernetes.io/name=git-k8s-deps || true
  k get validatingadmissionpolicies,validatingadmissionpolicybindings --show-labels || true
  k -n git-k8s get configmap git-k8s-checks -o yaml || true
  for program in git-k8s go-cache "${CHECKS[@]}"; do
    k -n "$(namespace_of "${program}")" describe pods || true
    k -n "$(namespace_of "${program}")" logs --all-containers --prefix --tail=200 -l "app.kubernetes.io/name=${program}" || true
  done
  echo "--- git server log"
  cat "${WORKDIR}/gitserver.log" || true
  echo "--- port-forward log"
  cat "${WORKDIR}/port-forward.log" || true
  echo "--- module proxy log"
  cat "${WORKDIR}/modproxy.log" || true
  echo "::endgroup::"
}

finish() {
  local status=$?
  # Deleting the cluster while kind creates it can leave a node behind, so
  # let kind finish first.
  if [[ -n "${KIND_PID}" ]]; then
    wait "${KIND_PID}" 2>/dev/null || true
  fi
  if [[ ${status} -ne 0 ]]; then
    diagnose
  fi
  for pid in "${PORT_FORWARD_PID}" "${PROBE_PID}" "${AGENT_IMAGE_PID}" "${GO_IMAGE_PID}" "${ZOMBIES_PID}" \
    "${GENERATING[@]}"; do
    if [[ -n "${pid}" ]]; then
      kill "${pid}" 2>/dev/null || true
    fi
  done
  if [[ "${GIT_K8S_KIND_KEEP:-}" == 1 ]]; then
    echo "Kept the cluster ${CLUSTER}, the registry ${REGISTRY}, and the git server and module proxy in ${WORKDIR}"
    exit "${status}"
  fi
  for pid in "${GIT_SERVER_PID}" "${MOD_PROXY_PID}"; do
    if [[ -n "${pid}" ]]; then
      kill "${pid}" 2>/dev/null || true
    fi
  done
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

# eventually runs a command until it succeeds, for up to $1 seconds. It
# tries again after a quarter of a second, then half a second, then every
# second, so a short wait ends soon and a long one doesn't keep a CPU busy
# that the cluster needs.
eventually() {
  local timeout=$1
  shift
  local deadline=$((SECONDS + timeout)) pause=0.25
  until "$@"; do
    if ((SECONDS >= deadline)); then
      echo "timed out after ${timeout}s: $*" >&2
      return 1
    fi
    sleep "${pause}"
    case "${pause}" in
      0.25) pause=0.5 ;;
      0.5) pause=1 ;;
    esac
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
need ssh-keygen
need curl
need timeout
install_kind
docker info >/dev/null

echo "::group::Start a registry, a kind cluster, a git server, and a module proxy"
# kind creates the cluster in the background while the test starts the
# registry, the git server, and the module proxy, and copies images to the
# registry.
if ! kind get clusters 2>/dev/null | grep -x "${CLUSTER}" >/dev/null; then
  CREATED_CLUSTER=1
  kind create cluster --name "${CLUSTER}" --wait 120s --config - >"${WORKDIR}/kind.log" 2>&1 <<EOF &
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
networking:
  kubeProxyMode: nftables
EOF
  KIND_PID=$!
fi
# As in https://kind.sigs.k8s.io/docs/user/local-registry/: nodes pull
# localhost:PORT/... from the registry container, which is on kind's
# network.
if [[ "$(docker inspect -f '{{.State.Running}}' "${REGISTRY}" 2>/dev/null || true)" != true ]]; then
  docker run -d --restart=always -p "127.0.0.1:${PORT}:5000" --name "${REGISTRY}" registry:2
  CREATED_REGISTRY=1
fi

(cd "${ROOT}" && go build -o "${WORKDIR}/gitserver" ./e2e/gitserver)
mkdir -p "${WORKDIR}/repos"
ssh-keygen -q -t ed25519 -N '' -C e2e@example.com -f "${WORKDIR}/e2e-key"
ssh-keygen -q -t ed25519 -N '' -C "${IDENTITY}" -f "${WORKDIR}/git-k8s-key"
printf 'e2e@example.com namespaces="git" %s\n%s namespaces="git" %s\n' \
  "$(cat "${WORKDIR}/e2e-key.pub")" "${IDENTITY}" "$(cat "${WORKDIR}/git-k8s-key.pub")" >"${ALLOWED_SIGNERS}"
GITSERVER_PASSWORD="${PASSWORD}" "${WORKDIR}/gitserver" -addr="0.0.0.0:${GIT_PORT}" -root="${WORKDIR}/repos" \
  -goproxy="${WORKDIR}/proxy" -allowed-signers="${ALLOWED_SIGNERS}" -kube-context="${CONTEXT}" \
  >"${WORKDIR}/gitserver.log" 2>&1 &
GIT_SERVER_PID=$!
HOST_URL="http://git-k8s:${PASSWORD}@127.0.0.1:${GIT_PORT}"
listening() { (echo >"/dev/tcp/127.0.0.1/${GIT_PORT}") 2>/dev/null; }
eventually 30 listening
# example.com/greet isn't on the internet, so test Pods can get it only
# through go-cache.
GREET="${WORKDIR}/modules/example.com/greet@v1.0.0"
mkdir -p "${GREET}"
printf 'module example.com/greet\n\ngo 1.24\n' >"${GREET}/go.mod"
printf 'package greet\n\nfunc Hello(name string) string { return "Hello, " + name }\n' >"${GREET}/greet.go"
(cd "${ROOT}" && go build -o "${WORKDIR}/modproxy" ./e2e/modproxy)
"${WORKDIR}/modproxy" -addr=0.0.0.0:0 -dir="${WORKDIR}/modules" >"${WORKDIR}/modproxy.log" 2>&1 &
MOD_PROXY_PID=$!
mod_port() { sed -nE 's/.* serving .* on .*:([0-9]+)$/\1/p' "${WORKDIR}/modproxy.log"; }
mod_proxy_listening() { [[ -n "$(mod_port)" ]]; }
eventually 30 mod_proxy_listening
MOD_PORT="$(mod_port)"
# Pods reach the git server on this machine through the gateway of kind's
# Docker network, which kind creates before the node.
kind_network() { docker network inspect kind >/dev/null 2>&1; }
eventually 120 kind_network
# The nodes reach the registry on kind's network. Connecting a container to
# a network briefly refuses connections to its published ports, so the
# registry joins kind's network before anything pushes to it.
if [[ "$(docker inspect -f '{{json .NetworkSettings.Networks.kind}}' "${REGISTRY}")" == null ]]; then
  docker network connect kind "${REGISTRY}"
fi
GATEWAY="$(docker network inspect kind -f '{{range .IPAM.Config}}{{.Gateway}} {{end}}' | tr ' ' '\n' |
  grep -E '^[0-9]+[.][0-9]+[.][0-9]+[.][0-9]+$' | head -n 1)"
CLUSTER_URL="http://${GATEWAY}:${GIT_PORT}"
# The gotest check's Pods use these images. Copying them into the local
# registry lets the nodes pull them without reaching the internet.
GO_IMAGE="localhost:${PORT}/chainguard/go:latest"
GIT_IMAGE="localhost:${PORT}/chainguard/git:latest"

# generate builds a program, pushes its image, and prints its manifests.
# While kind creates the cluster, the test generates the programs whose
# flags it knows, and the groups that install them apply their manifests.
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
# pregenerate NAME PROGRAM [FLAGS...] runs generate in the background, with
# the manifests in NAME.yaml and the log in NAME.log.
pregenerate() {
  local name=$1
  shift
  generate "$@" >"${WORKDIR}/${name}.yaml" 2>"${WORKDIR}/${name}.log" &
  GENERATING[${name}]=$!
}
# wait_generate NAME waits for pregenerate NAME to finish.
wait_generate() {
  if [[ -n "${GENERATING[$1]:-}" ]]; then
    GENERATED[$1]=0
    wait "${GENERATING[$1]}" || GENERATED[$1]=$?
    unset "GENERATING[$1]"
  fi
}
# generated NAME waits for pregenerate NAME, prints its log, and fails if
# generate failed.
generated() {
  wait_generate "$1"
  cat "${WORKDIR}/$1.log" >&2
  return "${GENERATED[$1]}"
}
# install_generated NAME applies the manifests of pregenerate NAME.
install_generated() {
  generated "$1"
  k apply -f "${WORKDIR}/$1.yaml"
}
# git-k8s installs the CustomResourceDefinitions that the checks watch, and
# the objects in config/policy.yaml. It runs one replica, the only writer of
# the mirror's volume, so no standby answers the checks' results with 503.
# The service account e2e-deps stands in for a controller that starts
# branches, and git-k8s-deps, which the deps group installs, starts deps/
# branches too. check-conflicts creates resolve/BRANCH. The test Pods'
# NetworkPolicy lets them reach go-cache.
pregenerate git-k8s git-k8s -- "-branch-prefix=${NS}/e2e-deps=deps/" \
  "-branch-prefix=git-k8s-deps/git-k8s-deps=deps/" \
  "-branch-prefix=check-conflicts/check-conflicts=resolve/" "-fake-github=${CLUSTER_URL}/github" \
  -go-cache-namespace=go-cache
crane() { go run github.com/google/go-containerregistry/cmd/crane@v0.22.1 "$@"; }
crane copy --platform "${PLATFORM}" "${CHAINGUARD}/go:latest" "${GO_IMAGE}"
crane copy --platform "${PLATFORM}" "${CHAINGUARD}/git:latest" "${GIT_IMAGE}"
# The other programs share most of git-k8s's packages, so they start once
# its generate has compiled them.
wait_generate git-k8s
pregenerate git-k8s-without-policies git-k8s -- -install-policies=false
pregenerate go-cache go-cache -base="${CHAINGUARD}/static:latest" -tmp-size=1Gi -- \
  "-upstream=http://${GATEWAY}:${MOD_PORT}" -max-size=512Mi
for program in "${CHECKS[@]}"; do
  case "${program}" in
    check-risk) pregenerate "${program}" "${program}" -- '-sensitive=auth/**' ;;
    check-gotest)
      pregenerate "${program}" "${program}" -- "-go-image=${GO_IMAGE}" "-git-image=${GIT_IMAGE}" -timeout=5m \
        -max-pods=1 -go-cache=http://go-cache.go-cache
      ;;
    check-approval) pregenerate "${program}" "${program}" -namespace="${APPROVAL_NS}" ;;
    *) pregenerate "${program}" "${program}" ;;
  esac
done
# The deps group installs go-cache again, with the git server's module
# proxy as its upstream.
pregenerate go-cache-deps go-cache -base="${CHAINGUARD}/static:latest" -tmp-size=1Gi -- \
  "-upstream=${CLUSTER_URL}/proxy" -max-size=512Mi

if [[ -n "${KIND_PID}" ]]; then
  kind_status=0
  wait "${KIND_PID}" || kind_status=$?
  KIND_PID=""
  cat "${WORKDIR}/kind.log"
  [[ ${kind_status} -eq 0 ]]
fi
NODES="$(kind get nodes --name "${CLUSTER}")"
for node in ${NODES}; do
  docker exec "${node}" mkdir -p "/etc/containerd/certs.d/localhost:${PORT}"
  printf '[host."http://%s:5000"]\n' "${REGISTRY}" |
    docker exec -i "${node}" cp /dev/stdin "/etc/containerd/certs.d/localhost:${PORT}/hosts.toml"
done
# Test Pods run in the Go image, so the nodes pull it in the background, and
# the group "Tests run in a sandboxed Pod" waits for them.
pull_go_image() {
  local node
  for node in ${NODES}; do
    docker exec "${node}" crictl pull "${GO_IMAGE}" || return
  done
}
pull_go_image >"${WORKDIR}/go-image.log" 2>&1 &
GO_IMAGE_PID=$!
k version
echo "Pods reach the git server at ${CLUSTER_URL}"
echo "go-cache fetches modules from http://${GATEWAY}:${MOD_PORT}"
echo "::endgroup::"

echo "::group::Install git-k8s with generate"
install_generated git-k8s
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
install_generated go-cache
k apply -f "${ROOT}/config/go-cache.yaml"
# policies_applied passes once each object in config/policy.yaml has the label
# that the core program sets when it applies them with the permissions that
# generate grants it.
policies_applied() {
  local owners
  owners="$(k get -f "${ROOT}/config/policy.yaml" \
    -o jsonpath='{range .items[*]}{.metadata.name} {.metadata.labels.kube\.imjasonh\.github\.io/managed-by}{"\n"}{end}')" &&
    [[ -n "${owners}" ]] && ! grep -vq ' git-k8s$' <<<"${owners}"
}
eventually 60 policies_applied
k get -f "${ROOT}/config/policy.yaml" --show-labels
# generate grants those permissions by name, and only to a program that
# installs the objects.
[[ "$(k auth can-i patch validatingadmissionpolicies.admissionregistration.k8s.io/other \
  --as=system:serviceaccount:git-k8s:git-k8s 2>/dev/null)" == no ]]
policy_names="$(k get -f "${ROOT}/config/policy.yaml" -o jsonpath='{range .items[*]}{.metadata.name}{"\n"}{end}')"
generated git-k8s-without-policies
# The results endpoint and the mirror read the git-k8s-checks ConfigMap, so
# the one rule that may name a ConfigMap or a policy is get on that ConfigMap
# alone. The rule ends where the next rule or object starts.
read_checks=$'- apiGroups:\n  - ""\n  resources:\n  - configmaps\n  resourceNames:\n  - git-k8s-checks\n  verbs:\n  - get\n-'
without_policies="$(<"${WORKDIR}/git-k8s-without-policies.yaml")"
if [[ "${without_policies}" != *"${read_checks}"* ]] ||
  grep -F -e configmaps -e "${policy_names}" <<<"${without_policies/"${read_checks}"/-}"; then
  echo "generate -- -install-policies=false must grant get on the git-k8s-checks ConfigMap, and nothing else that installs the policies" >&2
  exit 1
fi
# The results endpoint and the mirror treat a service account as a check
# only through its entry. The entries for the checks that later groups
# install go in now too, because the core program caches the entries for 5
# seconds, and a check that it rejects sends nothing more for a branch until
# the branch changes. The policies ignore the entry for the core program.
# Without that, it would make the core program the gofmt check, which can't
# write GitBranch status or change GitBranch objects, so nothing would land.
k -n git-k8s patch configmap git-k8s-checks --type=merge -p "data:
  check-base.check-base: base
  check-gofmt.check-gofmt: gofmt
  check-risk.check-risk: risk
  ${APPROVAL_NS}.check-approval: approval
  check-gotest.check-gotest: gotest
  check-review.check-review: review
  check-conflicts.check-conflicts: conflicts
  check-deps.check-deps: deps
  git-k8s.git-k8s: gofmt"
echo "::endgroup::"

echo "::group::Upgrading moves check results to the core program"
# Before the results endpoint, status.checks was a granular map, and each
# check controller applied its own entry. Stop the core program, put the map
# back the way an older release installed it, and apply two entries as the
# old check controllers did, one for a check that the policy doesn't list.
k -n git-k8s scale deployment/git-k8s --replicas=0
no_core_pods() { [[ -z "$(k -n git-k8s get pods -l app.kubernetes.io/name=git-k8s -o name)" ]]; }
eventually 120 no_core_pods
k patch crd gitbranches.git-k8s.imjasonh.com --type=json -p \
  '[{"op":"remove","path":"/spec/versions/0/schema/openAPIV3Schema/properties/status/properties/checks/x-kubernetes-map-type"}]'
OLD=1111111111111111111111111111111111111111
k create namespace git-k8s-upgrade
# Only the core program creates GitBranch objects.
k -n git-k8s-upgrade create --as=system:serviceaccount:git-k8s:git-k8s -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitBranch
metadata:
  name: app-c-old
spec:
  repository: app
  branch: c/old
  head: "${OLD}"
  parent: main
  parentHead: "2222222222222222222222222222222222222222"
  merge:
    checks:
      - name: gofmt
EOF
for check in gofmt risk; do
  k -n git-k8s-upgrade apply --server-side --subresource=status --field-manager="check-${check}" -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitBranch
metadata:
  name: app-c-old
status:
  checks:
    ${check}:
      commit: "${OLD}"
      scope: Head
      state: Failed
EOF
done
status_managers() {
  k -n git-k8s-upgrade get gitbranch app-c-old \
    -o jsonpath='{range .metadata.managedFields[?(@.subresource=="status")]}{.manager} {end}'
}
echo "Status managers before the upgrade: $(status_managers)"
k -n git-k8s scale deployment/git-k8s --replicas=1
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
old_field() { k -n git-k8s-upgrade get gitbranch app-c-old -o jsonpath="$1"; }
upgraded() {
  local managers
  managers=" $(status_managers) "
  [[ "${managers}" == *" results "* && "${managers}" != *" check-"* ]] &&
    [[ "$(old_field '{.status.checks.gofmt.commit}')" == "${OLD}" && -z "$(old_field '{.status.checks.risk}')" ]]
}
eventually 60 upgraded
echo "Status managers after the upgrade: $(status_managers)"
k delete namespace git-k8s-upgrade --wait=false
echo "The core program's results controller took over status.checks from the old check managers, kept the gofmt result, and removed the risk result."
echo "::endgroup::"

echo "::group::Install the checks"
# generate creates only the namespace named for the program.
k create namespace "${APPROVAL_NS}"
for program in "${CHECKS[@]}"; do
  install_generated "${program}"
done
for program in go-cache "${CHECKS[@]}"; do
  k -n "$(namespace_of "${program}")" rollout status "deployment/${program}" --timeout=180s
done
echo "::endgroup::"

# The agent group's image takes a while to build, so the test builds it and
# pushes it to the registry in the background while the groups before that
# one run.
AGENT_IMAGE="localhost:${PORT}/git-k8s-e2e/agent-runner"
build_agent_image() {
  docker build -q --platform "${PLATFORM}" --build-arg "CHAINGUARD=${CHAINGUARD}" -t "${AGENT_IMAGE}" "${ROOT}/agent/runner"
  docker push -q "${AGENT_IMAGE}"
  docker rmi "${AGENT_IMAGE}" >/dev/null || true
  crane digest "${AGENT_IMAGE}" >"${WORKDIR}/agent-image.digest"
}
build_agent_image >"${WORKDIR}/agent-image.log" 2>&1 &
AGENT_IMAGE_PID=$!

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
k -n "${NS}" create secret generic app-signing --type=kubernetes.io/ssh-auth \
  --from-file=ssh-privatekey="${WORKDIR}/git-k8s-key"
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
  signingKeyRef:
    name: app-signing
  pollInterval: 1s
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
        deleteLandedBranches: true
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
# A policy from another release makes the condition False until the core
# program restarts, which applies the policies from its own release again.
k annotate validatingadmissionpolicy git-k8s-check-results git-k8s.imjasonh.com/policy-version=1 --overwrite
policies_outdated() {
  [[ "$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="PoliciesInstalled")].reason}')" == Outdated ]]
}
eventually 60 policies_outdated
outdated="$(k -n "${NS}" get gitrepository app -o jsonpath='{.status.conditions[?(@.type=="PoliciesInstalled")].message}')"
echo "${outdated}"
[[ "${outdated}" == *"rollout restart deployment/git-k8s"* ]]
k -n git-k8s rollout restart deployment/git-k8s
k -n git-k8s rollout status deployment/git-k8s --timeout=180s
eventually 120 policies_installed
k -n "${NS}" get gitrepositories,gitbranches
echo "::endgroup::"

echo "::group::The API server takes only http and https URLs"
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
for url in '--upload-pack=touch /tmp/pwned' 'ssh://git@example.com/app.git' 'git@example.com:app.git' \
  'git://example.com/app.git' 'https://example.com/app.git?ref=main'; do
  if url_repository "${url}" | k apply --dry-run=server -f - 2>"${WORKDIR}/apply.err"; then
    echo "the API server accepted ${url}" >&2
    exit 1
  fi
  cat "${WORKDIR}/apply.err"
  grep -q 'spec.url' "${WORKDIR}/apply.err"
done
url_repository "https://git-k8s@${GATEWAY}:2222/app.git" | k apply --dry-run=server -f -
echo "The API server rejected a URL that git could read as an option and URLs that the mirror can't reach, and accepted an https URL."
echo "::endgroup::"

# forward_mirror port-forwards a local port to the core program's Service,
# which serves the mirror, and sets MIRROR to the base URL of NS's copies.
# A port-forward goes to one Pod, so it needs restarting with the Pod.
forward_mirror() {
  if [[ -n "${PORT_FORWARD_PID}" ]]; then
    kill "${PORT_FORWARD_PID}" 2>/dev/null || true
    wait "${PORT_FORWARD_PID}" 2>/dev/null || true
  fi
  # The background job truncates the log only once it starts, which can be
  # after forwarding first reads it. Truncate it here, so forwarding can't
  # match the last port-forward's lines.
  : >"${WORKDIR}/port-forward.log"
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
# mirror_head prints a ref's commit in the mirror's copy of repository $2,
# or app.
mirror_head() { mg "${DEPS_TOKEN}" ls-remote "${MIRROR}/${2:-app}.git" "$1" | cut -f1; }
# synced_condition prints a field of the ExternalSynced condition of
# repository $2, or app, which says whether the external repository has
# every change in the mirror.
synced_condition() {
  k -n "${NS}" get gitrepository "${2:-app}" -o jsonpath="{.status.conditions[?(@.type==\"ExternalSynced\")].$1}"
}
# in_sync reports whether repository $1, or app, is in sync.
in_sync() { [[ "$(synced_condition reason "${1:-app}")" == InSync ]]; }
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
# signed_by_git_k8s checks that commit $1 has a good signature from git-k8s's
# key, and git-k8s as its committer. $2 is the function that runs git in the
# repository that has the commit, g by default.
signed_by_git_k8s() {
  local run="${2:-g}"
  "${run}" verify-commit "$1"
  [[ "$("${run}" log -1 --format='%G? %GS %ce' "$1")" == "G ${IDENTITY} ${IDENTITY}" ]]
}
# zombies prints each zombie process on the cluster's nodes, with its parent.
# A process is a zombie from when it exits until its parent reaps it. In
# /proc/PID/stat, the state and the parent's PID follow the command name,
# which can contain spaces and ends at the last ")".
zombies() {
  local nodes node
  nodes="$(kind get nodes --name "${CLUSTER}")"
  [[ -n "${nodes}" ]]
  for node in ${nodes}; do
    docker exec "${node}" sh -c '
      node=$1
      for stat in /proc/[0-9]*/stat; do
        read -r line 2>/dev/null <"${stat}" || continue
        set -- ${line##*) }
        if [ "$1" = Z ]; then
          name="${line#*(}"
          echo "${node}: process ${line%% *} (${name%)*}), a child of $2 ($(cat "/proc/$2/comm" 2>/dev/null))"
        fi
      done' sh "${node}"
  done
}
# no_lasting_zombies fails if a zombie on the nodes is still one 10 seconds
# later, because then its parent doesn't reap it.
no_lasting_zombies() {
  local before after lasting
  before="$(zombies | sort)"
  sleep 10
  after="$(zombies | sort)"
  lasting="$(comm -12 <(echo "${before}") <(echo "${after}"))"
  if [[ -n "${lasting}" ]]; then
    echo "These zombies lasted 10 seconds:" >&2
    echo "${lasting}" >&2
    return 1
  fi
}

echo "::group::Failed git commands leave no zombies"
# When a fetch over HTTP fails, git exits without waiting for its remote
# helper, which then becomes a child of PID 1. Moving a repository away on
# the git server fails the core program's fetches from it. Checks fetch from
# the mirror, which refuses a check that none of the repository's merge
# policies list. An invalid pollInterval keeps the core program from
# changing the GitBranches, so c/gone's merge policy still lists risk, and
# once c/gone's result is removed, check-risk fetches c/gone again. risk's
# level is never none, so nothing lands, and the copy has no change that
# deleting the GitRepository has to push.
g push -q "${HOST_URL}/zombie.git" main
g checkout -q --detach
echo gone >"${WORK}/gone.txt"
g add gone.txt
g commit -qm "Add gone.txt"
gone="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/zombie.git" HEAD:refs/heads/c/gone
g checkout -q main
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: zombie
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/zombie.git
  secretRef:
    name: app-creds
  pollInterval: 1s
  branches:
    - match: main
      merge:
        checks:
          - name: risk
        when: checks.risk.outputs.level == "none"
    - match: c/**
      parent: main
EOF
gone_risk() { k -n "${NS}" get gitbranch "$(branch_object c/gone zombie)" -o jsonpath="{.status.checks.risk.$1}"; }
gone_checked() { [[ -n "$(branch_object c/gone zombie)" && "$(gone_risk commit)" == "${gone}" ]]; }
eventually 120 gone_checked
mv "${WORKDIR}/repos/zombie.git" "${WORKDIR}/repos/moved.git"
fetch_failed() { [[ "$(synced_condition reason zombie)" == SyncFailed && "$(synced_condition message zombie)" == *"not found"* ]]; }
eventually 60 fetch_failed
synced_condition message zombie
echo
k -n "${NS}" patch gitrepository zombie --type=json -p '[
  {"op": "replace", "path": "/spec/pollInterval", "value": "0s"},
  {"op": "remove", "path": "/spec/branches/0/merge"}]'
invalid_poll_interval() {
  [[ "$(k -n "${NS}" get gitrepository zombie -o jsonpath='{.status.conditions[?(@.type=="Ready")].reason}')" == InvalidPollInterval ]]
}
eventually 60 invalid_poll_interval
k -n "${NS}" patch gitbranch "$(branch_object c/gone zombie)" --subresource=status --type=json \
  -p '[{"op":"remove","path":"/status/checks/risk"}]'
risk_refused() { [[ "$(gone_risk state)" == Error && "$(gone_risk message)" == *"not found"* ]]; }
eventually 60 risk_refused
gone_risk message
echo
no_lasting_zombies
k -n "${NS}" delete gitrepository zombie
echo "The core program's fetches of a repository that moved and check-risk's fetches that the mirror refused failed, and no zombie on the nodes lasted 10 seconds."
echo "::endgroup::"

# kindnet, kind's network plugin, enforces NetworkPolicies only where the
# kernel has nfnetlink_queue. To find out, a Pod that a policy denies all
# egress tries to reach the git server until it can't. The plugin can take a
# few seconds to apply the policy to a new Pod, so the test decides that the
# cluster doesn't enforce NetworkPolicies only if the Pod still reaches the
# git server after 30 seconds. A try that can't connect lasts 20 seconds, so
# the probe runs in the background during the next groups, and the group
# "Tests run in a sandboxed Pod" waits for its answer. It starts after the
# zombie group, because a failed fetch can leave a zombie in its Pod. The
# test's own Pods, like check-gotest's, meet the restricted Pod Security
# Standard, so they start in a namespace that enforces it.
no_egress() {
  ! timeout 20 kubectl --context "${CONTEXT}" -n "${NS}" exec no-egress -- \
    git ls-remote --end-of-options "http://git-k8s:${PASSWORD}@${GATEWAY}:${GIT_PORT}/app.git" >/dev/null 2>&1
}
# probe_egress writes 1 to the file enforced if the cluster enforces
# NetworkPolicies, and 0 if it doesn't.
probe_egress() {
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
  if eventually 30 no_egress 2>/dev/null; then
    echo 1 >"${WORKDIR}/enforced"
  else
    echo 0 >"${WORKDIR}/enforced"
  fi
  k -n "${NS}" delete pod/no-egress networkpolicy/no-egress --wait=false
}
probe_egress >"${WORKDIR}/probe.log" 2>&1 &
PROBE_PID=$!

echo "::group::The git server rejects unsigned commits"
g checkout -q -b c/unsigned
echo unsigned >"${WORK}/unsigned.txt"
g add -A
g -c commit.gpgSign=false commit -qm "Add unsigned.txt"
if g push -q "${HOST_URL}/app.git" HEAD:c/unsigned 2>"${WORKDIR}/push.log"; then
  echo "the git server accepted an unsigned commit" >&2
  exit 1
fi
cat "${WORKDIR}/push.log"
grep -q "isn't signed with its committer's key" "${WORKDIR}/push.log"
g checkout -q main
echo "The git server rejected an unsigned commit, so git-k8s's commits land only if they're signed."
echo "::endgroup::"

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
# The mirror maps service accounts to checks as the results endpoint does:
# check-approval is the approval check, which main's merge policy lists,
# through its entry in the git-k8s-checks ConfigMap. The core program's
# entry names the gofmt check, but the core program is never a check.
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token "${APPROVAL_NS}" check-approval)")" == 200 ]]
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token git-k8s git-k8s)")" == 404 ]]
cat "${WORKDIR}/mirror.txt"
# Names don't make a check, because anyone who can create namespaces and
# service accounts can choose them: check-approval in the namespace
# check-approval has no entry, so it isn't the approval check.
k create namespace check-approval
k -n check-approval create serviceaccount check-approval
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token check-approval check-approval)")" == 404 ]]
cat "${WORKDIR}/mirror.txt"
# can_list_secrets reports whether service account $1, in namespace $2 or
# the namespace of the same name, can list or watch the Secrets in NS. A
# check that signs commits can get a Secret by name, for its signing key.
can_list_secrets() {
  local as="system:serviceaccount:${2:-$1}:$1"
  k auth can-i list secrets -n "${NS}" --as="${as}" || k auth can-i watch secrets -n "${NS}" --as="${as}"
}
for program in check-base check-gofmt check-risk check-approval check-gotest; do
  program_ns="$(namespace_of "${program}")"
  as="system:serviceaccount:${program_ns}:${program}"
  case "${program}" in
    check-base | check-gofmt)
      if can_list_secrets "${program}" "${program_ns}"; then
        echo "${program} can list Secrets" >&2
        exit 1
      fi
      ;;
    *)
      if k auth can-i get secrets -n "${NS}" --as="${as}"; then
        echo "${program} can read Secrets" >&2
        exit 1
      fi
      ;;
  esac
  if k -n "${program_ns}" auth can-i create "serviceaccounts/${program}" --subresource=token --as="${as}"; then
    echo "${program} can create tokens for its service account" >&2
    exit 1
  fi
done
k -n git-k8s auth can-i create serviceaccounts/git-k8s --subresource=token --as=system:serviceaccount:git-k8s:git-k8s
echo "Without a token, or with one for the API server, the mirror answers 401, and to a service account that isn't a check or a controller, 404. It maps check-approval in the namespace ${APPROVAL_NS} to the approval check through its ConfigMap entry, but not check-approval in the namespace check-approval, which has none, and never the core program. No check can create tokens, and only the core program can create tokens for Octo STS. The checks that don't sign commits can't read Secrets, and those that do can't list them."
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
signed_by_git_k8s FETCH_HEAD
eventually 60 branch_gone c/fmt
g log --oneline FETCH_HEAD
k -n git-k8s logs deployment/git-k8s >"${WORKDIR}/core.log"
grep -q 'served a push.*caller=check-gofmt/check-gofmt' "${WORKDIR}/core.log"
eventually 60 in_sync
[[ "$(mirror_head refs/heads/main)" == "$(remote_head main)" ]]
echo "The gofmt check pushed a signed fix to the mirror, main fast-forwarded to it in the mirror, the mirror synced main to the git server, and c/fmt was deleted."
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
# Three polls later, c/auth still hasn't landed.
sleep 3
[[ "$(remote_head main)" == "${main_before}" ]]
field '{.status.conditions[?(@.type=="Landed")].message}'
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
rejected "set ${APPROVE} to a commit's full SHA" annotate --as=alice "${APPROVE}=${AUTH:0:12}" "${APPROVED_BY}=alice"
# Only the core program changes a GitBranch's spec, which holds the merge
# policy, so neither alice, who can approve c/auth, nor bob, who can patch
# it, can drop its checks. Nobody else creates a GitBranch either.
for user in alice bob; do
  rejected "${user} can't change a GitBranch's spec" k -n "${NS}" patch gitbranch "$(branch_object c/auth)" \
    --as="${user}" --type=merge -p '{"spec":{"merge":{"when":"true"}}}'
done
rejected "can't create GitBranch objects; only the core program creates them" k -n "${NS}" create -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitBranch
metadata:
  name: app-c-forged
spec:
  repository: app
  branch: c/forged
  head: "${AUTH}"
  parent: main
  parentHead: "${main_before}"
  merge:
    when: "true"
EOF
# The gate wants alice's approval, so another approver's doesn't land c/auth.
admin="$(k auth whoami -o jsonpath='{.status.userInfo.username}')"
annotate "${APPROVE}=${AUTH}" "${APPROVED_BY}=${admin}"
approved_by() {
  [[ "$(field '{.status.checks.approval.state}')" == Passed ]] &&
    [[ "$(field '{.status.checks.approval.outputs.approver}')" == "$1" ]]
}
eventually 60 approved_by "${admin}"
gate_saw_approval() { field '{.status.conditions[?(@.type=="Landed")].message}' | grep -q 'approval Passed'; }
eventually 60 gate_saw_approval
[[ "$(field '{.status.state}')" == WaitingForChecks ]]
[[ "$(remote_head main)" == "${main_before}" ]]
rejected "remove ${APPROVED_BY} when you remove ${APPROVE}" annotate --as=alice "${APPROVE}-"
rejected "${APPROVED_BY} can change by itself only when you take over an approval" annotate --as=alice "${APPROVED_BY}-"
echo "The policies rejected bad approvals, changes to c/auth's spec, and a GitBranch that a person created, and c/auth waited through ${admin}'s approval."
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

echo "::group::An approved branch waits at the front of main's queue for the base check"
# main moves on, so c/auth is behind it, and so is c/ahead, another risky
# branch from where main was.
g checkout -q -B moved-again "${main_before}"
echo again >"${WORK}/again.txt"
g add -A
g commit -qm "Add again.txt"
g push -q "${HOST_URL}/app.git" HEAD:main
g checkout -q -B c/ahead "${main_before}"
main_before="$(g rev-parse moved-again)"
mkdir -p "${WORK}/auth"
printf 'package auth\n\n// First reports whether user goes first.\nfunc First(user string) bool { return user == "alice" }\n' \
  >"${WORK}/auth/first.go"
g add -A
g commit -qm "Add auth.First"
AHEAD="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:c/ahead
# behind_main reports whether the base check found branch $1 behind main at
# main_before, and the risk and gofmt checks finished with a high rating.
behind_main() {
  local object
  object="$(branch_object "$1")" && [[ -n "${object}" ]] &&
    [[ "$(k -n "${NS}" get gitbranch "${object}" -o jsonpath='{.status.checks.base.parentCommit} {.status.checks.base.outputs.behind} {.status.checks.risk.outputs.level} {.status.checks.gofmt.state}')" == "${main_before} true high Passed" ]]
}
eventually 120 behind_main c/auth
eventually 120 behind_main c/ahead
# With the base check stopped, the first branch in main's queue waits there
# for the base check to merge main in, and the branches behind it wait too.
k -n check-base scale deployment/check-base --replicas=0
base_stopped() { [[ -z "$(k -n check-base get pods -o name)" ]]; }
eventually 120 base_stopped
k -n "${NS}" annotate --overwrite gitbranch "$(branch_object c/ahead)" --as=alice "${APPROVE}=${AHEAD}" "${APPROVED_BY}=alice"
waiting_for_base() {
  [[ "$(k -n "${NS}" get gitbranch "$(branch_object c/ahead)" -o jsonpath='{.status.conditions[?(@.type=="Landed")].message}')" == \
    "first in main's queue; waiting for the base check to merge main in" ]]
}
eventually 60 waiting_for_base
echo "alice approved c/ahead, which waits at the front of main's queue for the base check to merge main in."
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
queue_is() { [[ "$(k -n "${NS}" get gitbranch "$(branch_object main)" -o jsonpath='{.status.queue[*]}')" == "$1" ]]; }
eventually 60 queue_is "c/ahead c/auth"
echo "bob couldn't take over ${admin}'s approval, and alice could, so the gate passed and c/auth joined main's queue behind c/ahead."
echo "::endgroup::"

echo "::group::Approvals and risk ratings hold through the base check's merges"
timeout 600 kubectl --context "${CONTEXT}" -n "${NS}" get gitbranches -l git-k8s.imjasonh.com/repository=app --watch \
  -o jsonpath='{.spec.branch}: {.status.checks.approval.message}{"\n"}' >"${WORKDIR}/approvals.txt" 2>&1 &
approvals_pid=$!
k -n check-base scale deployment/check-base --replicas=1
k -n check-base rollout status deployment/check-base --timeout=180s
risky_landed() {
  branch_gone c/ahead && branch_gone c/auth && fetch_main &&
    g cat-file -e FETCH_HEAD:auth/first.go && g cat-file -e FETCH_HEAD:auth/policy.go
}
eventually 240 risky_landed
kill "${approvals_pid}" 2>/dev/null || true
wait "${approvals_pid}" || true
g log --graph --format='%h %s' "${main_before}^..FETCH_HEAD"
# The base check merged main into c/ahead at the front of the queue, and
# then into c/auth, after c/ahead landed.
[[ "$(g log -1 --format=%s FETCH_HEAD)" == "Merge main into c/auth" ]]
[[ "$(g log -1 --format=%s FETCH_HEAD^2)" == "Merge main into c/ahead" ]]
[[ "$(g rev-parse FETCH_HEAD^1 FETCH_HEAD^2^1 FETCH_HEAD^2^2)" == "$(printf '%s\n' "${AUTH}" "${AHEAD}" "${main_before}")" ]]
# Each merge makes the change that alice approved, so it kept her approval
# and check-risk's rating.
grep -Fx "c/ahead: ${AHEAD:0:12} is approved by alice, and $(g rev-parse --short=12 FETCH_HEAD^2) makes the same change" "${WORKDIR}/approvals.txt"
grep -Fx "c/auth: ${AUTH:0:12} is approved by alice, and $(g rev-parse --short=12 FETCH_HEAD) makes the same change" "${WORKDIR}/approvals.txt"
k -n check-risk logs deployment/check-risk >"${WORKDIR}/risk.log"
grep -E 'kept a result for the same change.+ branch=c/ahead ' "${WORKDIR}/risk.log"
grep -E 'kept a result for the same change.+ branch=c/auth ' "${WORKDIR}/risk.log"
echo "The base check merged main into c/ahead and then c/auth at the front of main's queue, and both landed with alice's approvals and check-risk's ratings of the commits before the merges."
echo "::endgroup::"

echo "::group::Two branches behind main land through its queue in turn"
fetch_main
g checkout -q -B c/one FETCH_HEAD
echo one >"${WORK}/one.txt"
g add -A
g commit -qm "Add one.txt"
ONE="$(g rev-parse HEAD)"
g checkout -q -B c/two FETCH_HEAD
echo two >"${WORK}/two.txt"
g add -A
g commit -qm "Add two.txt"
TWO="$(g rev-parse HEAD)"
g checkout -q -B moved FETCH_HEAD
echo three >"${WORK}/three.txt"
g add -A
g commit -qm "Add three.txt"
MOVED="$(g rev-parse HEAD)"
g push -q "${HOST_URL}/app.git" HEAD:main
timeout 600 kubectl --context "${CONTEXT}" -n "${NS}" get gitbranch "$(branch_object main)" --watch \
  -o jsonpath='{.status.queue[*]}{"\n"}' >"${WORKDIR}/queues.txt" 2>&1 &
queues_pid=$!
g push -q "${HOST_URL}/app.git" c/one:c/one c/two:c/two
both_landed() {
  branch_gone c/one && branch_gone c/two && fetch_main &&
    g cat-file -e FETCH_HEAD:one.txt && g cat-file -e FETCH_HEAD:two.txt
}
eventually 240 both_landed
kill "${queues_pid}" 2>/dev/null || true
wait "${queues_pid}" || true
echo "main's queue as it changed:"
cat "${WORKDIR}/queues.txt"
grep -Eqx 'c/(one|two) c/(one|two)' "${WORKDIR}/queues.txt"
g log --graph --format='%h %G? %GS %s' FETCH_HEAD
# Each branch merged main in once: the first merged MOVED and landed, and
# the second merged the first's landing.
[[ "$(g log --format=%s "${MOVED}..FETCH_HEAD" | grep -c '^Merge main into c/')" == 2 ]]
[[ "$(g rev-parse FETCH_HEAD^2^2)" == "${MOVED}" ]]
[[ "$(g rev-parse FETCH_HEAD^1 FETCH_HEAD^2^1 | sort)" == "$(printf '%s\n' "${ONE}" "${TWO}" | sort)" ]]
g log --format=%B FETCH_HEAD | grep -x 'Git-K8s-Fixer: base' >/dev/null
signed_by_git_k8s FETCH_HEAD
signed_by_git_k8s FETCH_HEAD^2
echo "Both branches waited in main's queue, and each merged main in once, at the front, with a signed merge, before it landed."
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
signed_by_git_k8s FETCH_HEAD
echo "The gofmt check fixed c/squash, and main moved by one signed, squashed commit without the fixer trailer."
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
for commit in $(g rev-list "${rebase_base}..FETCH_HEAD"); do
  signed_by_git_k8s "${commit}"
done
g cat-file -e FETCH_HEAD:main.txt
echo "The base check merged main into c/rebase, and main moved by signed copies of its two commits, without the merge."
echo "::endgroup::"

echo "::group::Only the core program writes check results"
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
result='{"status":{"checks":{"gofmt":{"commit":"0000000","scope":"Head","state":"Passed"}}}}'
approval_result='{"status":{"checks":{"approval":{"commit":"0000000","scope":"Head","state":"Passed"}}}}'
diverged='{"status":{"diverged":{"commit":"0000000","ref":"refs/git-k8s/downstream/heads/main"}}}'
approval_token="$(k -n "${APPROVAL_NS}" create token check-approval)"
for bearer in "${token}" "${approval_token}"; do
  code="$(patch_status "${result}" "${bearer}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 403 ]]
  grep -q 'cannot patch resource' "${WORKDIR}/patch.json"
  grep -q 'gitbranches/status' "${WORKDIR}/patch.json"
done
# Checks read the tokens for the results endpoint and the mirror that generate
# mounts in their Pods, so no check may create tokens, for its own service
# account or for another.
[[ "$(k auth can-i create serviceaccounts/check-approval --subresource=token -n "${APPROVAL_NS}" --as="system:serviceaccount:${APPROVAL_NS}:check-approval")" == no ]]
[[ "$(k auth can-i create serviceaccounts/check-risk --subresource=token -n check-risk --as=system:serviceaccount:check-gofmt:check-gofmt)" == no ]]
[[ "$(k auth can-i create serviceaccounts/git-k8s --subresource=token -n git-k8s --as=system:serviceaccount:check-gofmt:check-gofmt)" == no ]]

# The results endpoint takes a check's result only with a token for the
# check's own service account and the endpoint's audience. It shares the
# core program's Service and port with the mirror.
forward_mirror
send_result() {
  curl -sS -o "${WORKDIR}/result.txt" -w '%{http_code}' -X PUT -H "Authorization: ${3:-Bearer} $1" \
    -H 'Content-Type: application/json' --data '{"commit":"0000000","scope":"Head","state":"Passed"}' \
    "${MIRROR%/"${NS}"}/results/${NS}/$(branch_object main)/$2"
}
risk_token="$(k -n check-risk create token check-risk --audience=git-k8s-results)"
code="$(send_result "${risk_token}" gofmt)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 403 ]]
grep -q "check-risk is the risk check, so it can't write the gofmt check's result" "${WORKDIR}/result.txt"
code="$(send_result "${token}" gofmt)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 401 ]]
# The scheme is case-insensitive.
code="$(send_result "${risk_token}" risk bearer)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 409 ]]
grep -q "main has no parent, so it takes no check results" "${WORKDIR}/result.txt"
# check-approval is the approval check through its entry in the ConfigMap.
# The core program's entry names the gofmt check, but the core program is
# never a check.
approval_results_token="$(k -n "${APPROVAL_NS}" create token check-approval --audience=git-k8s-results)"
code="$(send_result "${approval_results_token}" approval)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 409 ]]
grep -q "main has no parent, so it takes no check results" "${WORKDIR}/result.txt"
code="$(send_result "${approval_results_token}" gofmt)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 403 ]]
grep -q "system:serviceaccount:${APPROVAL_NS}:check-approval is the approval check, so it can't write the gofmt check's result" "${WORKDIR}/result.txt"
core_results_token="$(k -n git-k8s create token git-k8s --audience=git-k8s-results)"
code="$(send_result "${core_results_token}" gofmt)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 403 ]]
grep -q "system:serviceaccount:git-k8s:git-k8s isn't a check's service account" "${WORKDIR}/result.txt"
# Nor is check-approval in the namespace check-approval, which has no entry.
squatter_results_token="$(k -n check-approval create token check-approval --audience=git-k8s-results)"
code="$(send_result "${squatter_results_token}" approval)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 403 ]]
grep -q "system:serviceaccount:check-approval:check-approval isn't a check's service account; add an entry for check-approval.check-approval to the git-k8s-checks ConfigMap" "${WORKDIR}/result.txt"
# A cache miss doesn't show that a GitBranch is gone, so the results
# endpoint reads the API server, and answers 410 at once rather than after
# its 10-second wait for the cache.
start="${SECONDS}"
code="$(curl -sS -o "${WORKDIR}/result.txt" -w '%{http_code}' -X PUT -H "Authorization: Bearer ${risk_token}" \
  -H 'Content-Type: application/json' --data '{"commit":"0000000","scope":"Head","state":"Passed"}' \
  "${MIRROR%/"${NS}"}/results/${NS}/app-no-such-branch/risk?generation=1")"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 410 ]]
grep -q "GitBranch ${NS}/app-no-such-branch doesn't exist" "${WORKDIR}/result.txt"
((SECONDS - start < 5))
# Each endpoint accepts only tokens for its own audience, even from a check
# that the other endpoint accepts.
code="$(send_result "$(mirror_token check-risk check-risk)" risk)"
cat "${WORKDIR}/result.txt"
[[ "${code}" == 401 ]]
[[ "$(info_refs -H "Authorization: Bearer ${risk_token}")" == 401 ]]
cat "${WORKDIR}/mirror.txt"
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token check-risk check-risk)")" == 200 ]]

# If a role lets a check or another service account write status anyway,
# the admission policy still lets only the core program write results and
# status.diverged. It rejects any status write from a check, including a
# merge queue, and a change to either from any other service account.
k -n "${NS}" create serviceaccount rogue
k apply -f - <<EOF
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: git-k8s-e2e-status
rules:
  - apiGroups: [git-k8s.imjasonh.com]
    resources: [gitbranches/status]
    verbs: [patch]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: git-k8s-e2e-status
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: git-k8s-e2e-status
subjects:
  - kind: ServiceAccount
    namespace: check-gofmt
    name: check-gofmt
  - kind: ServiceAccount
    namespace: ${APPROVAL_NS}
    name: check-approval
  - kind: ServiceAccount
    namespace: ${NS}
    name: rogue
EOF
rogue_token="$(k -n "${NS}" create token rogue)"
status_rejected() { [[ "$(patch_status "$1" "$2")" == 422 ]] && grep -q "$3" "${WORKDIR}/patch.json"; }
for patch in "${result}" '{"status":{"checks":{"risk":{"commit":"0000000","scope":"Head","state":"Passed"}}}}' \
  '{"status":{"queued":{"since":"2026-01-01T00:00:00Z","head":"0000000"}}}' \
  '{"status":{"queue":["c/x"]}}' "${diverged}"; do
  eventually 30 status_rejected "${patch}" "${token}" "the gofmt check can't write GitBranch status"
  cat "${WORKDIR}/patch.json"
  echo
done
# check-approval is a check only through its entry in the ConfigMap.
eventually 30 status_rejected "${approval_result}" "${approval_token}" "the approval check can't write GitBranch status"
cat "${WORKDIR}/patch.json"
echo
eventually 30 status_rejected "${result}" "${rogue_token}" "system:serviceaccount:${NS}:rogue isn't the core program's service account"
cat "${WORKDIR}/patch.json"
echo
eventually 30 status_rejected "${diverged}" "${rogue_token}" "system:serviceaccount:${NS}:rogue isn't the core program's service account, so it can't write status.diverged"
cat "${WORKDIR}/patch.json"
echo
# The policies ignore the core program's entry, which names the gofmt check.
core_token="$(k -n git-k8s create token git-k8s)"
[[ "$(patch_status "${result}" "${core_token}")" == 200 ]]
[[ "$(patch_status "${diverged}" "${core_token}")" == 200 ]]
k -n "${NS}" patch gitbranch "$(branch_object main)" --subresource=status --type=merge --dry-run=server -p "${result}"
k delete clusterrolebinding,clusterrole git-k8s-e2e-status
echo "The results endpoint takes a check's result only with the check's own token, and the endpoint and the policy map check-approval in the namespace ${APPROVAL_NS} to the approval check through its ConfigMap entry, but never the core program. The endpoint refuses check-approval in the namespace check-approval, which has no entry. The results endpoint answers 410 at once for a GitBranch that doesn't exist. It refuses a check's token for the mirror, and the mirror refuses its token for the results endpoint. Checks can't write GitBranch status, a merge queue, or status.diverged even with a role that allows it. The core program and people can write status.checks, the core program can write status.diverged, and other service accounts can write neither."
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
# names a full SHA and itself in approved-by, which git-k8s-approvals
# allows, can't approve.
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
  cant_approve "${sa}" "{\"metadata\":{\"annotations\":{\"${APPROVE}\":\"$(remote_head main)\",\"${APPROVED_BY}\":\"system:serviceaccount:${sa}:${sa}\"}}}"
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
# A finalizer would keep the GitBranch after its branch is deleted, and an
# owner reference to a missing ConfigMap would make garbage collection
# delete it. Without the core program's entries in managedFields, its
# server-side applies would leave behind the fields that they stop setting.
hold='{"metadata":{"finalizers":["example.com/hold"]}}'
reown='{"metadata":{"ownerReferences":[{"apiVersion":"v1","kind":"ConfigMap","name":"gone","uid":"6d9e4f0c-0000-4000-8000-000000000000"}]}}'
reset='{"metadata":{"managedFields":[{}]}}'
for patch in '{"metadata":{"labels":{"e2e":"changed"}}}' "${hold}" "${reown}" "${reset}"; do
  code="$(patch_branch "${gotest_token}" "${patch}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]]
  grep -q "the gotest check can't change GitBranch objects" "${WORKDIR}/patch.json"
done
# check-gofmt and check-approval own nothing, so generate doesn't let them
# patch GitBranch objects at all.
approve='{"metadata":{"annotations":{"git-k8s.imjasonh.com/approve":"0000000"}}}'
for bearer in "${token}" "${approval_token}"; do
  code="$(patch_branch "${bearer}" "${approve}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 403 ]]
  grep -q 'cannot patch resource' "${WORKDIR}/patch.json"
done
echo "Neither a check nor the core controller can approve a branch or take over its approval, a check can't change one, and check-gofmt and check-approval can't patch one."
echo "::endgroup::"

echo "::group::A check that the ConfigMap names can't change GitBranch objects or their status"
# bot has the permissions that generate gives check-gotest, so RBAC lets it
# patch GitBranch objects. generate gives no check a role to write their
# status, so another role lets bot write it, and only the policy stops it. bot
# runs in the namespace ${APPROVAL_NS}, so only its entry in the
# git-k8s-checks ConfigMap makes it a check.
k -n "${APPROVAL_NS}" create serviceaccount bot
k create clusterrolebinding git-k8s-e2e-bot --clusterrole=check-gotest --serviceaccount="${APPROVAL_NS}:bot"
k apply -f - <<EOF
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: git-k8s-e2e-bot-status
rules:
  - apiGroups: [git-k8s.imjasonh.com]
    resources: [gitbranches/status]
    verbs: [patch]
---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: git-k8s-e2e-bot-status
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: git-k8s-e2e-bot-status
subjects:
  - kind: ServiceAccount
    namespace: ${APPROVAL_NS}
    name: bot
EOF
k -n git-k8s patch configmap git-k8s-checks --type=merge -p "{\"data\":{\"${APPROVAL_NS}.bot\":\"bot\"}}"
bot_token="$(k -n "${APPROVAL_NS}" create token bot)"
# bot_cant_change passes if the API server rejects bot's patch of a label with
# the message $1.
bot_cant_change() {
  local code
  code="$(patch_branch "${bot_token}" '{"metadata":{"labels":{"e2e":"changed"}}}')"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]] && grep -qF "$1" "${WORKDIR}/patch.json"
}
eventually 30 bot_cant_change "the bot check can't change GitBranch objects"
# bot_cant_write_status passes if the API server rejects bot's patch of a
# merge queue with the message $1.
bot_cant_write_status() {
  local code
  code="$(patch_status '{"status":{"queue":["c/x"]}}' "${bot_token}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]] && grep -qF "$1" "${WORKDIR}/patch.json"
}
eventually 30 bot_cant_write_status "the bot check can't write GitBranch status; it sends its results to the core program"
# An empty entry stops bot from sending results, and RBAC still lets it patch
# GitBranch objects and their status.
k -n git-k8s patch configmap git-k8s-checks --type=merge -p "{\"data\":{\"${APPROVAL_NS}.bot\":\"\"}}"
eventually 30 bot_cant_change \
  "system:serviceaccount:${APPROVAL_NS}:bot, a check whose entry in the git-k8s-checks ConfigMap is empty, can't change GitBranch objects"
eventually 30 bot_cant_write_status \
  "system:serviceaccount:${APPROVAL_NS}:bot, a check whose entry in the git-k8s-checks ConfigMap is empty, can't write a GitBranch's status"
k delete clusterrolebinding,clusterrole git-k8s-e2e-bot-status
echo "RBAC lets bot patch GitBranch objects and, through a role that generate gives no check, their status, and the policies stop it both as the bot check that its ConfigMap entry names and after the entry is emptied."
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
sync_failed() { [[ "$(synced_condition reason "${1:-app}")" == SyncFailed ]]; }
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
    -c user.name=e2e -c user.email=e2e@example.com "${SIGN[@]}" "$@"
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
# deleteLandedBranches, so the check runs can be checked afterward.
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
  signingKeyRef:
    name: app-signing
  pollInterval: 1s
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
o fetch -q "${GITHUB_URL}/acme/octo.git" main
signed_by_git_k8s "${fix}" o
# check_run prints the status and conclusion of check $2's check run on
# commit $1.
check_run() {
  curl -fsS "${GITHUB_URL}/api/v3/repos/acme/octo/commits/$1/check-runs?check_name=git-k8s/$2" |
    sed -nE 's/.*"status":"([a-z_]+)","conclusion":"([a-z_]*)".*/\1 \2/p'
}
# check-gofmt reports Fixed for the unformatted commit after it pushes the
# fix. The repositories controller syncs octo every second, and a sync
# that's running when the push arrives can move c/fmt to the fix first.
# Then the core program refuses the result, which isn't for c/fmt's head,
# and the unformatted commit gets no gofmt check run. If it gets one, it's
# neutral, and the check-runs controller creates it before the fix's gofmt
# check run, so once the fix's check runs show their results, it doesn't
# change.
check_runs_published() {
  [[ "$(check_run "${fix}" gofmt)" == "completed success" &&
    "$(check_run "${fix}" base)" == "completed success" ]] || return
  local unformatted_run
  unformatted_run="$(check_run "${unformatted}" gofmt)"
  [[ -z "${unformatted_run}" || "${unformatted_run}" == "completed neutral" ]]
}
eventually 60 check_runs_published
echo "check-gofmt pushed a signed fix to the mirror, git-k8s landed it and pushed it to GitHub with Octo STS tokens, and the results became check runs."

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
probe_status=0
wait "${PROBE_PID}" || probe_status=$?
PROBE_PID=""
cat "${WORKDIR}/probe.log"
[[ ${probe_status} -eq 0 ]]
go_image_status=0
wait "${GO_IMAGE_PID}" || go_image_status=$?
GO_IMAGE_PID=""
cat "${WORKDIR}/go-image.log"
[[ ${go_image_status} -eq 0 ]]
ENFORCED="$(cat "${WORKDIR}/enforced")"
if [[ ${ENFORCED} -eq 0 ]]; then
  echo "This cluster doesn't enforce NetworkPolicies, so the test doesn't check what test Pods can reach."
fi

TESTED="${WORKDIR}/tested"
git init -q -b main "${TESTED}"
t() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${TESTED}" \
    -c user.name=e2e -c user.email=e2e@example.com "${SIGN[@]}" "$@"
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
  # which on a one-node cluster include the API server. The policy drops
  # the connections, so each dial lasts its whole timeout, and the test dials
  # all three at once. It dials addresses, not names, so the timeout is all
  # for the connection, and 1.5 seconds lets the kernel send a lost SYN
  # again, which it does after a second.
  cat >"${TESTED}/sandbox_test.go" <<GO
package tested

import (
	"net"
	"sync"
	"testing"
	"time"
)

func TestSandbox(t *testing.T) {
	dns, err := net.LookupHost("kube-dns.kube-system.svc.cluster.local")
	if err != nil {
		t.Fatalf("looking up CoreDNS: %v", err)
	}
	var wg sync.WaitGroup
	for _, addr := range []string{"${GATEWAY}:${GIT_PORT}", net.JoinHostPort(dns[0], "9153"), "1.1.1.1:53"} {
		wg.Add(1)
		go func() {
			defer wg.Done()
			if c, err := net.DialTimeout("tcp", addr, 1500*time.Millisecond); err == nil {
				c.Close()
				t.Errorf("the test Pod reached %s", addr)
			}
		}()
	}
	wg.Wait()
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
  pollInterval: 1s
  branches:
    - match: main
      merge:
        checks:
          - name: gotest
        deleteLandedBranches: true
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
# the Pods with check-gotest's controller label. The mirror lets a gotest
# result's Pod fetch only with that label, so the test Pods that fetched
# have it, even where the cluster doesn't enforce the policy.
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
# service account or a person can. A result counts only on a branch whose
# merge policy lists gotest, so the result goes on c/named in tested. Until
# c/named is gone, check-gotest, which would replace the result, stops. The
# mirror lets a token that's bound to the Pod fetch only while the Pod has
# check-gotest's controller label, isn't being deleted, and is Pending, as
# check-gotest's Pods are while their init container fetches. gotest-named
# stays Pending because its init container waits. That container ignores
# SIGTERM, so a deleted Pod stays in its 30-second grace period, while the
# API server still accepts its token. gotest-running has no init container,
# so it runs.
k -n check-gotest scale deployment/check-gotest --replicas=0
gotest_stopped() { [[ -z "$(k -n check-gotest get pods -o name)" ]]; }
eventually 120 gotest_stopped
t checkout -q -b c/named
t commit -q --allow-empty -m "Name a test Pod"
t push -q --end-of-options "${HOST_URL}/tested.git" HEAD:c/named
named_listed() { [[ -n "$(branch_object c/named tested)" ]]; }
eventually 60 named_listed
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
# named_result writes a gotest result that names Pod $1 on branch $2 of
# repository $3, or on c/named of tested.
named_result() {
  k -n "${NS}" patch gitbranch "$(branch_object "${2:-c/named}" "${3:-tested}")" --subresource=status --type=merge \
    -p '{"status":{"checks":{"gotest":{"commit":"0000000","scope":"Head","state":"Running","pod":"'"$1"'"}}}}' >/dev/null
}
# pod_token prints a token for the mirror that's bound to Pod $1.
pod_token() {
  k -n "${NS}" create token default --audience=git-k8s-mirror --bound-object-kind=Pod \
    --bound-object-name="$1" --bound-object-uid="$(k -n "${NS}" get pod "$1" -o jsonpath='{.metadata.uid}')"
}
# tested_refs is info_refs for tested's copy.
tested_refs() {
  curl -sS -o "${WORKDIR}/mirror.txt" -w '%{http_code}' "$@" "${MIRROR}/tested.git/info/refs?service=git-upload-pack"
}
# main has no parent, so no merge policy applies to it, and a result on app's
# main doesn't count. The mirror reads results in the order that they're
# written, so once the result on c/named counts, it has read this one too.
named_result gotest-named main app
named_result gotest-named
named_token="$(pod_token gotest-named)"
named_fetch() { tested_refs -H "Authorization: Bearer ${named_token}"; }
named_fetches() { [[ "$(named_fetch)" == 200 ]]; }
eventually 30 named_fetches
[[ "$(info_refs -H "Authorization: Bearer ${named_token}")" == 404 ]]
k -n "${NS}" label pod gotest-named --overwrite kube.imjasonh.github.io/controller=check-other
[[ "$(named_fetch)" == 404 ]]
k -n "${NS}" label pod gotest-named kube.imjasonh.github.io/controller-
[[ "$(named_fetch)" == 404 ]]
[[ "$(info_refs -H "Authorization: Bearer $(mirror_token "${NS}" default)")" == 404 ]]
[[ "$(tested_refs -H "Authorization: Bearer $(mirror_token "${NS}" default)")" == 404 ]]
k -n "${NS}" label pod gotest-named kube.imjasonh.github.io/controller=check-gotest
[[ "$(named_fetch)" == 200 ]]
# Once gotest-named can't fetch, the mirror has the result that names
# gotest-running, so the mirror refuses gotest-running only because it runs.
named_result gotest-running
named_refused() { [[ "$(named_fetch)" == 404 ]]; }
eventually 30 named_refused
[[ "$(info_refs -H "Authorization: Bearer $(pod_token gotest-running)")" == 404 ]]
[[ "$(tested_refs -H "Authorization: Bearer $(pod_token gotest-running)")" == 404 ]]
named_result gotest-named
eventually 30 named_fetches
k -n "${NS}" delete pod gotest-named --wait=false
[[ "$(named_fetch)" == 404 ]]
k -n "${NS}" delete pod gotest-named gotest-running --grace-period=0 --force --ignore-not-found 2>/dev/null
k -n "${NS}" patch gitbranch "$(branch_object main)" --subresource=status --type=merge \
  -p '{"status":{"checks":{"gotest":null}}}' >/dev/null
t push -q --delete --end-of-options "${HOST_URL}/tested.git" c/named
named_gone() { [[ -z "$(branch_object c/named tested)" ]]; }
eventually 60 named_gone
k -n check-gotest scale deployment/check-gotest --replicas=1
k -n check-gotest rollout status deployment/check-gotest --timeout=180s
echo "A Pending Pod that a gotest result names fetched with check-gotest's label, and not with another check's label, without the label, or while it was being deleted. A running Pod that the result named couldn't fetch, and neither could the same service account's token without a Pod. Only a result on a branch whose merge policy lists gotest counted, and only in that branch's repository."
echo "::endgroup::"

echo "::group::A burst of branches takes turns under -max-pods=1"
# Each branch's test sleeps, so Pods that ran at once would overlap. The
# branches start from main's parent, so they pass without landing.
# tested's merge policy has no base check, so the branches don't queue, and
# none of them goes first as the front of a queue.
# c/burst-a sorts first, but it's pushed after the others are waiting.
burst=(c/burst-b c/burst-c c/burst-d)
for b in "${burst[@]}" c/burst-a; do
  t checkout -q -b "${b}" "${tested_main}"
  cat >"${TESTED}/slow_test.go" <<'GO'
package tested

import (
	"testing"
	"time"
)

func TestSlow(t *testing.T) { time.Sleep(5 * time.Second) }
GO
  t add slow_test.go
  t commit -qm "Test slowly on ${b}"
done
# burst_results prints each tested branch's name, head, and gotest commit,
# state, and waiting time.
burst_results() {
  k -n "${NS}" get gitbranches -l git-k8s.imjasonh.com/repository=tested -o jsonpath='{range .items[*]}{.spec.branch}|{.spec.head}|{.status.checks.gotest.commit}|{.status.checks.gotest.state}|{.status.checks.gotest.notes.waiting}{"\n"}{end}'
}
burst_checked() { [[ "$(burst_results | awk -F'|' '$1 ~ /^c\/burst-[bcd]$/ && $2 == $3' | wc -l)" -eq 3 ]]; }
t push -q "${HOST_URL}/tested.git" "${burst[@]}"
eventually 120 burst_checked
t push -q "${HOST_URL}/tested.git" c/burst-a

declare -A waited=() finished=()
order=()
most=0
deadline=$((SECONDS + 600))
while ((${#finished[@]} < 4)); do
  if ((SECONDS >= deadline)); then
    echo "timed out; started: ${order[*]}" >&2
    exit 1
  fi
  running="$(k -n "${NS}" get pods -l app.kubernetes.io/name=check-gotest \
    -o jsonpath='{range .items[*]}{.status.phase}{"\n"}{end}' | grep -cvE '^(Succeeded|Failed)$' || true)"
  if ((running > most)); then
    most=${running}
  fi
  while IFS='|' read -r branch head commit state since; do
    if [[ "${branch}" != c/burst-* || "${commit}" != "${head}" ]]; then
      continue
    fi
    if [[ -n "${since}" ]]; then
      waited[${branch}]=${since}
    elif [[ " ${order[*]} " != *" ${branch} "* ]]; then
      order+=("${branch}")
    fi
    if [[ "${state}" == Passed || "${state}" == Failed ]]; then
      finished[${branch}]=${state}
    fi
  done < <(burst_results)
  sleep 1
done
for b in "${order[@]}"; do
  echo "${b} started after waiting since ${waited[${b}]:-never}, and ${finished[${b}]}"
done
echo "Most test Pods running at once: ${most}"
((most == 1))
for b in "${order[@]}"; do
  [[ "${finished[${b}]}" == Passed ]]
done
# Only the first branch found a free place. The others started in the order
# that they started waiting, which put c/burst-a last.
[[ ${#order[@]} -eq 4 && -z "${waited[${order[0]}]:-}" ]]
for b in "${order[@]:1}"; do
  [[ -n "${waited[${b}]:-}" ]]
done
by_wait="$(for b in "${order[@]:1}"; do echo "${waited[${b}]} ${b}"; done | LC_ALL=C sort | cut -d' ' -f2 | paste -sd' ')"
[[ "${by_wait}" == "${order[*]:1}" && "${order[3]}" == c/burst-a ]]
t push -q --delete "${HOST_URL}/tested.git" "${burst[@]}" c/burst-a
burst_gone() {
  local results
  results="$(burst_results)" && [[ "${results}" != *c/burst-* ]]
}
eventually 60 burst_gone
eventually 60 no_test_pods
echo "Four branches ran one at a time, in the order that they started waiting."
echo "::endgroup::"

echo "::group::Test Pods get modules and build outputs from go-cache"
# With -go-cache-namespace, the core program's NetworkPolicy lets test Pods
# reach go-cache, as well as the mirror and CoreDNS.
policy_reaches_go_cache() {
  [[ "$(k -n "${NS}" get networkpolicy tested-test-pods \
    -o jsonpath='{.spec.egress[*].to[*].namespaceSelector.matchLabels.kubernetes\.io/metadata\.name}')" == *go-cache* ]]
}
eventually 30 policy_reaches_go_cache
metrics() { k get --raw /api/v1/namespaces/go-cache/services/go-cache:http/proxy/metrics; }
# metric prints the value of a sample, such as
# go_cache_module_requests_total{result="hit"}, from the metrics in file $1.
metric() { awk -v sample="$2" '$1 == sample { print $2 }' "$1"; }
# grew prints how much sample $3 grew from metrics file $1 to file $2.
grew() { echo $(($(metric "$2" "$3") - $(metric "$1" "$3"))); }
GET_HIT='go_cache_build_requests_total{method="GET",result="hit"}'
GET_MISS='go_cache_build_requests_total{method="GET",result="miss"}'
PUT_CREATED='go_cache_build_requests_total{method="PUT",result="created"}'
PUT_DENIED='go_cache_build_requests_total{method="PUT",result="denied"}'
MOD_FETCHED='go_cache_module_requests_total{result="fetched"}'
MOD_HIT='go_cache_module_requests_total{result="hit"}'
metrics >"${WORKDIR}/metrics-0.txt"

t checkout -q -b c/greet "${fixed}"
printf '\nrequire example.com/greet v1.0.0\n' >>"${TESTED}/go.mod"
printf 'package tested\n\nimport "example.com/greet"\n\n// Greeting greets the cluster.\nfunc Greeting() string { return greet.Hello("kind") }\n' \
  >"${TESTED}/greeting.go"
cat >"${TESTED}/greeting_test.go" <<'GO'
package tested

import "testing"

func TestGreeting(t *testing.T) {
	if got := Greeting(); got != "Hello, kind" {
		t.Errorf("Greeting() = %q, want %q", got, "Hello, kind")
	}
}
GO
GOPROXY="http://127.0.0.1:${MOD_PORT}" GOSUMDB=off GOFLAGS=-modcacherw GOMODCACHE="${WORKDIR}/gomodcache" \
  go -C "${TESTED}" mod tidy
t add -A
t commit -qm "Greet the cluster"
greet="$(t rev-parse HEAD)"
t push -q "${HOST_URL}/tested.git" HEAD:c/greet
greet_landed() { [[ "$(remote_head main tested)" == "${greet}" ]]; }
eventually 300 greet_landed
eventually 60 no_test_pods
metrics >"${WORKDIR}/metrics-1.txt"
(($(grew "${WORKDIR}/metrics-0.txt" "${WORKDIR}/metrics-1.txt" "${MOD_FETCHED}") > 0))

# A Pod with check-gotest's controller label, which the core program's
# NetworkPolicy selects, tries to reach the module proxy itself. kind's
# network plugin enforces NetworkPolicies, except on hosts that lack the
# kernel support that it needs. Like a test Pod, the probe meets the
# restricted Pod Security Standard.
k apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: np-probe
  namespace: ${NS}
  labels:
    kube.imjasonh.github.io/controller: check-gotest
spec:
  restartPolicy: Never
  activeDeadlineSeconds: 30
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: probe
      image: ${GO_IMAGE}
      command: [go, mod, download, -x, example.com/greet@v1.0.0]
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
      env:
        - {name: HOME, value: /tmp}
        - {name: GOFLAGS, value: -modcacherw}
        - {name: GOPROXY, value: "http://${GATEWAY}:${MOD_PORT}"}
        - {name: GOSUMDB, value: "off"}
        - {name: GOTOOLCHAIN, value: local}
EOF
probe_phase() { k -n "${NS}" get pod np-probe -o jsonpath='{.status.phase}'; }
probe_done() { [[ "$(probe_phase)" == Succeeded || "$(probe_phase)" == Failed ]]; }
eventually 120 probe_done
k -n "${NS}" logs np-probe --tail=5 || true
if [[ "$(probe_phase)" == Succeeded ]]; then
  echo "This cluster doesn't enforce NetworkPolicies, so test Pods could have reached the module proxy."
else
  echo "The NetworkPolicy kept a test Pod from reaching the module proxy."
fi
k -n "${NS}" delete pod np-probe

# go-cache serves the module from its store now.
kill "${MOD_PROXY_PID}"
wait "${MOD_PROXY_PID}" 2>/dev/null || true
MOD_PROXY_PID=""
t checkout -q -b c/greet-docs
printf '# tested\n\nGreeting greets the cluster.\n' >"${TESTED}/README.md"
t add -A
t commit -qm "Add a README"
docs="$(t rev-parse HEAD)"
t push -q "${HOST_URL}/tested.git" HEAD:c/greet-docs
docs_landed() { [[ "$(remote_head main tested)" == "${docs}" ]]; }
eventually 300 docs_landed
eventually 60 no_test_pods
metrics >"${WORKDIR}/metrics-2.txt"
m1="${WORKDIR}/metrics-1.txt"
m2="${WORKDIR}/metrics-2.txt"
grep '^go_cache_' "${m2}"
stored="$(grew "${WORKDIR}/metrics-0.txt" "${m1}" "${PUT_CREATED}")"
read_back="$(grew "${m1}" "${m2}" "${GET_HIT}")"
missed="$(grew "${m1}" "${m2}" "${GET_MISS}")"
stored_again="$(grew "${m1}" "${m2}" "${PUT_CREATED}")"
(($(grew "${m1}" "${m2}" "${MOD_HIT}") > 0 && $(grew "${m1}" "${m2}" "${MOD_FETCHED}") == 0))
((read_back >= 100 && stored_again < 10))
# go-cache turned away none of check-gotest's uploads.
(($(metric "${m2}" "${PUT_DENIED}") == 0))
echo "c/greet's Pod got example.com/greet through go-cache and stored ${stored} build outputs."
echo "With the module proxy stopped, c/greet-docs's Pod got the module from go-cache's store, read ${read_back} build outputs, missed ${missed}, and stored ${stored_again}."
echo "::endgroup::"

echo "::group::Only check-gotest's Pending Pods write to the build caches"
# Two Pods get tokens that can write tested's build cache. check-gotest
# doesn't own cache-writer, and a scheduling gate keeps it Pending, so it
# never runs. cache-runner has check-gotest's label, and runs.
k apply -f - <<EOF
apiVersion: v1
kind: Pod
metadata:
  name: cache-writer
  namespace: ${NS}
spec:
  schedulingGates:
    - name: git-k8s.imjasonh.com/e2e
  automountServiceAccountToken: false
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: writer
      image: ${GO_IMAGE}
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
---
apiVersion: v1
kind: Pod
metadata:
  name: cache-runner
  namespace: ${NS}
  labels:
    kube.imjasonh.github.io/controller: check-gotest
spec:
  automountServiceAccountToken: false
  terminationGracePeriodSeconds: 1
  securityContext:
    runAsNonRoot: true
    runAsUser: 65532
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: runner
      image: ${GO_IMAGE}
      command: [sleep, "600"]
      securityContext:
        allowPrivilegeEscalation: false
        capabilities:
          drop: [ALL]
EOF
# write_token prints a token that can write tested's build cache, bound to
# the Pod named $1.
write_token() {
  k -n "${NS}" create token default --duration=10m \
    --audience="git-k8s.imjasonh.com/go-cache/write/${NS}/tested" \
    --bound-object-kind=Pod --bound-object-name="$1"
}
writer_token="$(write_token cache-writer)"
cache_ip="$(k -n go-cache get service go-cache -o jsonpath='{.spec.clusterIP}')"
probe_output="$(printf probe | sha256sum | cut -d ' ' -f 1)"
# put_probe uploads an output with token $2 while its Pod is $1, from a
# node, which reaches go-cache's Service like a test Pod. It writes the
# response to /tmp/probe.txt on the node, logs the status and the body, and
# prints the status.
put_probe() {
  local action code
  action="$(printf '%s' "$1" | sha256sum | cut -d ' ' -f 1)"
  code="$(docker exec "${CLUSTER}-control-plane" curl -sS -o /tmp/probe.txt -w '%{http_code}' -X PUT \
    -H "Authorization: Bearer $2" -H "Go-Output-Id: ${probe_output}" \
    --data-binary probe "http://${cache_ip}/cache/${NS}/tested/${action}")"
  echo "A write while the Pod is $1: ${code} $(docker exec "${CLUSTER}-control-plane" cat /tmp/probe.txt)" >&2
  echo "${code}"
}
pod_phase() { k -n "${NS}" get pod "$1" -o jsonpath='{.status.phase}'; }
code="$(put_probe unlabeled "${writer_token}")"
[[ "${code}" == 403 ]]
docker exec "${CLUSTER}-control-plane" grep -q "Pod ${NS}/cache-writer isn't check-gotest's" /tmp/probe.txt
# Anyone who can create Pods in the namespace can set check-gotest's label.
# go-cache remembers for 10 seconds that the Pod failed the check.
k -n "${NS}" label pod cache-writer kube.imjasonh.github.io/controller=check-gotest
[[ "$(pod_phase cache-writer)" == Pending ]]
labeled() { [[ "$(put_probe labeled "${writer_token}")" == 201 ]]; }
eventually 30 labeled
k -n "${NS}" delete pod cache-writer
code="$(put_probe deleted "${writer_token}")"
[[ "${code}" == 403 ]]
# check-gotest's Pods upload from an init container, while they're Pending.
runner_running() { [[ "$(pod_phase cache-runner)" == Running ]]; }
eventually 120 runner_running
runner_token="$(write_token cache-runner)"
code="$(put_probe running "${runner_token}")"
[[ "${code}" == 403 ]]
docker exec "${CLUSTER}-control-plane" grep -q "Pod ${NS}/cache-runner is Running, not Pending" /tmp/probe.txt
k -n "${NS}" delete pod cache-runner
echo "go-cache turned away a token from a Pod without check-gotest's label, took it once the Pending Pod had the label, and turned it away once the Pod was gone. It turned away a token from a Running Pod with the label."
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

echo "::group::An agent reviews branches in sandboxed Pods"
# The fake backend fails added lines that hold DO NOT MERGE and deletes them
# when the check may push, so the test needs no Cursor API key.
agent_image_status=0
wait "${AGENT_IMAGE_PID}" || agent_image_status=$?
AGENT_IMAGE_PID=""
cat "${WORKDIR}/agent-image.log"
[[ ${agent_image_status} -eq 0 ]]
AGENT_IMAGE="${AGENT_IMAGE}@$(<"${WORKDIR}/agent-image.digest")"
CHECKS+=(check-review)
install check-review -- "-agent-image=${AGENT_IMAGE}" "-git-image=${GIT_IMAGE}" -backend=fake -timeout=5m
# The conflicts and deps groups install programs whose flags name the image.
pregenerate check-conflicts check-conflicts -- "-agent-image=${AGENT_IMAGE}" "-git-image=${GIT_IMAGE}" \
  -backend=fake -timeout=5m
pregenerate check-deps check-deps -- "-agent-image=${AGENT_IMAGE}" "-git-image=${GIT_IMAGE}" -backend=fake \
  -timeout=5m
pregenerate git-k8s-deps git-k8s-deps -- "-goproxy=${CLUSTER_URL}/proxy" -gosumdb=off "-go-image=${GO_IMAGE}" \
  "-git-image=${GIT_IMAGE}" "-result-image=${AGENT_IMAGE}" -interval=1s -min-age=5s -timeout=5m
k -n check-review rollout status deployment/check-review --timeout=180s
# The agent Pods fetch from the mirror with tokens that kube binds to them,
# so check-review needs no repository credentials. It gets Secrets only by
# name, for its signing key.
review_sa=system:serviceaccount:check-review:check-review
if can_list_secrets check-review; then
  echo "check-review can list Secrets" >&2
  exit 1
fi
if k -n check-review auth can-i create serviceaccounts/check-review --subresource=token --as="${review_sa}"; then
  echo "check-review can create tokens for its service account" >&2
  exit 1
fi
REVIEWED="${WORKDIR}/reviewed"
git init -q -b main "${REVIEWED}"
rv() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${REVIEWED}" \
    -c user.name=e2e -c user.email=e2e@example.com "${SIGN[@]}" "$@"
}
printf 'Notes\n' >"${REVIEWED}/notes.txt"
rv add -A
rv commit -qm "Add notes"
rv push -q "${HOST_URL}/reviewed.git" HEAD:main HEAD:draft
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: reviewed
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/reviewed.git
  secretRef:
    name: app-creds
  signingKeyRef:
    name: app-signing
  pollInterval: 1s
  branches:
    - match: main
      merge:
        checks:
          - name: review
            mayPush: true
        deleteLandedBranches: true
    - match: c/**
      parent: main
    - match: draft
      merge:
        checks:
          - name: review
        maxAgentRuns: 1
    - match: d/**
      parent: draft
EOF
review() { k -n "${NS}" get gitbranch "$(branch_object "$1" reviewed)" -o jsonpath="{.status.checks.review.$2}"; }
no_agent_pods() { [[ -z "$(k -n "${NS}" get pods -l app.kubernetes.io/name=git-k8s-agent -o name)" ]]; }

rv checkout -q -b c/marked
printf 'Notes\nDO NOT MERGE\nMore notes\n' >"${REVIEWED}/notes.txt"
rv commit -qam "Add more notes"
rv push -q "${HOST_URL}/reviewed.git" HEAD:c/marked
fixed_on_main() {
  rv fetch -q "${HOST_URL}/reviewed.git" main &&
    [[ "$(rv show FETCH_HEAD:notes.txt)" == "$(printf 'Notes\nMore notes')" ]]
}
eventually 300 fixed_on_main
rv log -1 --format=%B FETCH_HEAD
rv log -1 --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Fixer: review'
signed_by_git_k8s FETCH_HEAD rv
marked_gone() { [[ -z "$(remote_head c/marked reviewed)" && -z "$(branch_object c/marked reviewed)" ]]; }
eventually 60 marked_gone
eventually 60 no_agent_pods

rv checkout -q -b d/marked main
printf 'Notes\nDO NOT MERGE\n' >"${REVIEWED}/notes.txt"
rv commit -qam "Mark the notes"
rv push -q "${HOST_URL}/reviewed.git" HEAD:d/marked
review_failed() { [[ -n "$(branch_object d/marked reviewed)" && "$(review d/marked state)" == Failed ]]; }
eventually 300 review_failed
k -n "${NS}" get gitbranch "$(branch_object d/marked reviewed)" -o jsonpath='{.status.checks.review}'
echo
[[ "$(review d/marked message)" == "The change adds DO NOT MERGE at notes.txt:2." ]]
[[ "$(review d/marked notes.summary)" == "1 added line holds DO NOT MERGE" ]]
[[ "$(review d/marked notes.model)" == fake:composer-2.5 ]]
[[ "$(review d/marked notes.inputTokens)" -gt 0 ]]
[[ "$(review d/marked notes.runs)" == 1 ]]
eventually 60 no_agent_pods
printf 'Notes\nDO NOT MERGE\nDO NOT MERGE EITHER\n' >"${REVIEWED}/notes.txt"
rv commit -qam "Mark the notes again"
marked_again="$(rv rev-parse HEAD)"
rv push -q "${HOST_URL}/reviewed.git" HEAD:d/marked
out_of_runs() { [[ "$(review d/marked commit)" == "${marked_again}" && "$(review d/marked state)" == Running ]]; }
eventually 120 out_of_runs
review d/marked message
echo
review d/marked message | grep -q 'the branch used all 1 agent runs that maxAgentRuns allows'
no_agent_pods
echo "check-review can't list Secrets or create tokens. The agent's signed fix, from a Pod that fetched from the mirror, landed on main, its review failed a branch that the check can't push to, and that branch's next head waits for an agent run."
echo "::endgroup::"

echo "::group::Conflicts with a parent that moved are resolved before branches land"
# Git merges go.sum with its union driver. The fake agent resolves other
# conflicts by keeping the branch's lines and then the parent's, and fails a
# conflict that holds DO NOT MERGE.
CHECKS+=(check-conflicts)
install_generated check-conflicts
k -n check-conflicts rollout status deployment/check-conflicts --timeout=180s
# The check and its agent Pods fetch from the mirror, and the check pushes
# to it, so check-conflicts needs no repository credentials either. It gets
# Secrets only by name, for its signing key.
conflicts_sa=system:serviceaccount:check-conflicts:check-conflicts
if can_list_secrets check-conflicts; then
  echo "check-conflicts can list Secrets" >&2
  exit 1
fi
if k -n check-conflicts auth can-i create serviceaccounts/check-conflicts --subresource=token --as="${conflicts_sa}"; then
  echo "check-conflicts can create tokens for its service account" >&2
  exit 1
fi
echo "check-conflicts can't list Secrets or create tokens."
CONFLICTED="${WORKDIR}/conflicted"
mkdir "${CONFLICTED}"
cf() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_ALLOW_PROTOCOL=http:https:git:ssh \
    git -C "${CONFLICTED}" -c user.name=e2e -c user.email=e2e@example.com "${SIGN[@]}" "$@"
}
cf init -q -b main
printf 'example.com/a v1.0.0 h1:a=\n' >"${CONFLICTED}/go.sum"
printf 'Notes\n' >"${CONFLICTED}/notes.txt"
cf add -A
cf commit -qm "Add go.sum and notes"
cf push -q --end-of-options "${HOST_URL}/conflicted.git" HEAD:main
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: conflicted
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/conflicted.git
  secretRef:
    name: app-creds
  signingKeyRef:
    name: app-signing
  pollInterval: 1s
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: conflicts
            mayPush: true
        deleteLandedBranches: true
    - match: c/**
      parent: main
EOF
result() { k -n "${NS}" get gitbranch "$(branch_object "$1" conflicted)" -o jsonpath="{.status.checks.$2.$3}"; }
# race_main sets the file $2 to $3 and then $4 on a new branch $1 from main,
# and to $3 and then $5 on main. It pushes main first, so that the branch
# conflicts with main when git-k8s first sees it.
race_main() {
  cf switch -q -c "$1" --end-of-options main
  printf '%b%s\n' "$3" "$4" >"${CONFLICTED}/$2"
  cf commit -qam "Change $2 on $1"
  cf switch -q --end-of-options main
  printf '%b%s\n' "$3" "$5" >"${CONFLICTED}/$2"
  cf commit -qam "Change $2 on main"
  cf push -q --end-of-options "${HOST_URL}/conflicted.git" main:main
  cf push -q --end-of-options "${HOST_URL}/conflicted.git" "$1:$1"
}
# landed_with reports whether the branch $1 landed and is gone, and main's
# file $2 holds $3.
landed_with() {
  [[ -z "$(remote_head "$1" conflicted)" && -z "$(branch_object "$1" conflicted)" ]] &&
    cf fetch -q --end-of-options "${HOST_URL}/conflicted.git" main &&
    [[ "$(cf show --end-of-options FETCH_HEAD:"$2")" == "$3" ]]
}
# merged_main checks that main's head, in FETCH_HEAD, is the conflicts
# check's signed merge of the main that race_main pushed into the branch $1.
# It saves the message instead of piping it to grep, because grep -q can exit
# before git log finishes writing, and pipefail then fails on git's SIGPIPE.
merged_main() {
  local message
  message="$(cf log -1 --format=%B --end-of-options FETCH_HEAD)"
  echo "${message}"
  grep -qx 'Git-K8s-Fixer: conflicts' <<<"${message}"
  [[ "$(cf log -1 --format=%P --end-of-options FETCH_HEAD)" == "$(cf rev-parse --verify --end-of-options "$1") $(cf rev-parse --verify --end-of-options main)" ]]
  signed_by_git_k8s FETCH_HEAD cf
}

race_main c/sum go.sum 'example.com/a v1.0.0 h1:a=\n' 'example.com/b v1.0.0 h1:b=' 'example.com/c v1.0.0 h1:c='
eventually 300 landed_with c/sum go.sum "$(printf 'example.com/a v1.0.0 h1:a=\nexample.com/b v1.0.0 h1:b=\nexample.com/c v1.0.0 h1:c=')"
merged_main c/sum
echo "Git merged the go.sum conflict with its union driver, the check signed the merge, and c/sum landed."

cf switch -q -C main --end-of-options FETCH_HEAD
race_main c/text notes.txt 'Notes\n' 'The branch adds this line.' 'Main adds this line.'
eventually 300 landed_with c/text notes.txt "$(printf 'Notes\nThe branch adds this line.\nMain adds this line.')"
merged_main c/text
eventually 60 no_agent_pods
echo "The agent, in a Pod that fetched from the mirror, resolved the notes.txt conflict, the check signed its merge, and c/text landed."

cf switch -q -C main --end-of-options FETCH_HEAD
race_main c/refused notes.txt 'Notes\nThe branch adds this line.\nMain adds this line.\n' 'DO NOT MERGE' 'Main adds another line.'
refused="$(cf rev-parse --verify --end-of-options c/refused)"
moved="$(cf rev-parse --verify --end-of-options main)"
refused_failed() {
  [[ -n "$(branch_object c/refused conflicted)" && "$(result c/refused conflicts state)" == Failed &&
    "$(result c/refused base outputs.conflicts)" == notes.txt ]]
}
eventually 300 refused_failed
k -n "${NS}" get gitbranch "$(branch_object c/refused conflicted)" -o jsonpath='{.status.checks}'
echo
[[ "$(result c/refused conflicts message)" == "the agent couldn't resolve the conflicts: The conflicts in notes.txt hold DO NOT MERGE or aren't well formed, so the fake agent changed no files." ]]
[[ "$(result c/refused conflicts notes.runs)" == 1 ]]
[[ "$(remote_head c/refused conflicted)" == "${refused}" ]]
[[ "$(remote_head main conflicted)" == "${moved}" ]]
eventually 60 no_agent_pods
echo "The base check reported the notes.txt conflict on c/refused, and the agent refused to resolve it, so c/refused stays as it is."
echo "::endgroup::"

echo "::group::The conflicts check resolves a divergence and a rewind through the mirror"
# c/refused can't land, so it stays while both sides change it. As with
# deps/x, a wrong password keeps the mirror from the git server while a
# commit goes to each side. The commit in the mirror comes from the base
# check, which main's merge policy lets push to c/refused, and the commit in
# the git server comes from a person.
forward_mirror
BASE_TOKEN="$(mirror_token check-base check-base)"
# diverge_refused pushes commit $1 to c/refused in the mirror, and forces
# commit $2 onto c/refused in the git server, while the mirror can't reach
# the git server.
diverge_refused() {
  k -n "${NS}" patch secret app-creds --type=merge -p '{"stringData":{"password":"wrong"}}'
  eventually 90 sync_failed conflicted
  cf -c "http.extraHeader=Authorization: Bearer ${BASE_TOKEN}" push -q --end-of-options "${MIRROR}/conflicted.git" "$1:refs/heads/c/refused"
  cf push -q --force --end-of-options "${HOST_URL}/conflicted.git" "$2:refs/heads/c/refused"
  k -n "${NS}" patch secret app-creds --type=merge -p "{\"stringData\":{\"password\":\"${PASSWORD}\"}}"
}
# refused_resolved reports whether the mirror and the git server have
# c/refused at the same commit, which is neither $1 nor $2, with no
# divergence left, and fetches that commit into FETCH_HEAD.
refused_resolved() {
  local tip
  tip="$(remote_head c/refused conflicted)"
  [[ -n "${tip}" && "${tip}" != "$1" && "${tip}" != "$2" &&
    "$(mirror_head refs/heads/c/refused conflicted)" == "${tip}" &&
    -z "$(k -n "${NS}" get gitbranch "$(branch_object c/refused conflicted)" -o jsonpath='{.status.diverged}')" ]] &&
    in_sync conflicted &&
    cf fetch -q --end-of-options "${HOST_URL}/conflicted.git" c/refused
}

cf switch -q -C in-mirror --end-of-options "${refused}"
printf 'fix\n' >"${CONFLICTED}/fix.txt"
cf add -A
cf commit -qm "Add a fix" -m "Git-K8s-Fixer: base"
base_fix="$(cf rev-parse --verify --end-of-options HEAD)"
cf switch -q -C in-external --end-of-options "${refused}"
printf 'person\n' >"${CONFLICTED}/person.txt"
cf add -A
cf commit -qm "Add a person's change"
person="$(cf rev-parse --verify --end-of-options HEAD)"
diverge_refused "${base_fix}" "${person}"
eventually 300 refused_resolved "${base_fix}" "${person}"
merge_message="$(cf log -1 --format=%B --end-of-options FETCH_HEAD)"
echo "${merge_message}"
[[ "$(head -n 1 <<<"${merge_message}")" == "Merge the external repository's c/refused into c/refused" ]]
grep -qx 'Git-K8s-Fixer: conflicts' <<<"${merge_message}"
[[ "$(cf log -1 --format=%P --end-of-options FETCH_HEAD)" == "${base_fix} ${person}" ]]
signed_by_git_k8s FETCH_HEAD cf
[[ "$(remote_head main conflicted)" == "${moved}" ]]
merged="$(cf rev-parse --verify --end-of-options FETCH_HEAD)"
echo "c/refused changed both in the mirror and in the git server, and the conflicts check pushed a signed merge of the git server's head to the mirror, which pushed it to the git server."

# The git server rewinds c/refused, which drops the merge and the commits
# under it, while the base check adds a commit in the mirror. A merge of
# the two heads would bring back the dropped commits, so the check replays
# the mirror's commit onto the git server's head instead. fix2.txt doesn't
# hold fix.txt's content, because git would take the replay's new file for
# fix.txt renamed, and the rewind deleted fix.txt, so the check's merges
# would conflict and it would leave the divergence for a person.
cf switch -q -C in-mirror --end-of-options "${merged}"
printf 'another fix\n' >"${CONFLICTED}/fix2.txt"
cf add -A
cf commit -qm "Add another fix" -m "Git-K8s-Fixer: base"
base_fix2="$(cf rev-parse --verify --end-of-options HEAD)"
cf switch -q -C in-external --end-of-options "${refused}"
printf 'rewritten\n' >"${CONFLICTED}/rewritten.txt"
cf add -A
cf commit -qm "Rewrite the branch"
rewritten="$(cf rev-parse --verify --end-of-options HEAD)"
diverge_refused "${base_fix2}" "${rewritten}"
eventually 300 refused_resolved "${base_fix2}" "${rewritten}"
cf log -1 --format='%B%nauthor %an <%ae>, committer %cn <%ce>' --end-of-options FETCH_HEAD
[[ "$(cf log -1 --format=%P --end-of-options FETCH_HEAD)" == "${rewritten}" ]]
[[ "$(cf log -1 --format='%an %ae%n%B' --end-of-options FETCH_HEAD)" == "$(cf log -1 --format='%an %ae%n%B' --end-of-options "${base_fix2}")" ]]
signed_by_git_k8s FETCH_HEAD cf
[[ "$(cf show --end-of-options FETCH_HEAD:fix2.txt)" == "another fix" && "$(cf show --end-of-options FETCH_HEAD:rewritten.txt)" == rewritten ]]
[[ -z "$(cf ls-tree --name-only --end-of-options FETCH_HEAD fix.txt person.txt)" ]]
[[ "$(remote_head main conflicted)" == "${moved}" ]]
eventually 60 no_agent_pods
echo "The git server rewound c/refused while the base check added a commit in the mirror, and the conflicts check replayed that commit onto the git server's head, so the commits that the rewind dropped stayed out."
echo "::endgroup::"

echo "::group::A controller keeps Go modules up to date on branches"
# The deps repository requires example.com/greet from the git server's
# module proxy. git-k8s-deps takes a version only once it's 5 seconds old,
# both since git-k8s-deps first saw it and by the proxy's time for it, so
# the versions that it should take are backdated.
(cd "${ROOT}" && go build -o "${WORKDIR}/publish" ./e2e/publish)
publish() {
  local dir
  dir="$(mktemp -d "${WORKDIR}/greet.XXXXXX")"
  printf 'module example.com/greet\n\ngo 1.24\n' >"${dir}/go.mod"
  printf 'package greet\n\n%s\n' "$3" >"${dir}/greet.go"
  "${WORKDIR}/publish" -root="${WORKDIR}/proxy" -dir="${dir}" -version="$1" -time="$2"
}
long_ago=2020-01-01T00:00:00Z
publish v1.0.0 "${long_ago}" 'func Hello() string { return "hello" }'
DEPS="${WORKDIR}/deps"
git init -q -b main "${DEPS}"
dg() {
  GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 git -C "${DEPS}" \
    -c user.name=e2e -c user.email=e2e@example.com "${SIGN[@]}" "$@"
}
printf 'module example.com/deps\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n' >"${DEPS}/go.mod"
# The fake agent replaces a line that holds FAKE AGENT FIX with the text
# after it, which calls Hello as v1.1.0 declares it.
cat >"${DEPS}/greeting.go" <<'GO'
package deps

import "example.com/greet"

// Greeting greets the world.
func Greeting() string {
	return greet.Hello() + ", world" // FAKE AGENT FIX: return greet.Hello("world")
}
GO
cat >"${DEPS}/greeting_test.go" <<'GO'
package deps

import "testing"

func TestGreeting(t *testing.T) {
	if got := Greeting(); got != "hello, world" {
		t.Errorf("Greeting() = %q, want %q", got, "hello, world")
	}
}
GO
# The go command on PATH can be older than the module's go line, so use the
# toolchain that git-k8s's go.mod selects.
go_cmd="$(cd "${ROOT}" && go env GOROOT)/bin/go"
(cd "${DEPS}" && GOPROXY="http://127.0.0.1:${GIT_PORT}/proxy" GOSUMDB=off GOFLAGS=-modcacherw \
  GOMODCACHE="${WORKDIR}/modcache" "${go_cmd}" mod tidy)
dg add -A
dg commit -qm "Greet the world"
dg push -q "${HOST_URL}/deps.git" HEAD:main
k apply -f - <<EOF
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: deps
  namespace: ${NS}
spec:
  url: ${CLUSTER_URL}/deps.git
  secretRef:
    name: app-creds
  signingKeyRef:
    name: app-signing
  pollInterval: 1s
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: gotest
          - name: deps
            mayPush: true
          - name: risk
          - name: approval
        when: >-
          checks.base.passed && checks.gotest.passed && checks.deps.passed &&
          (checks.risk.outputs.level == "low" || checks.approval.passed)
        deleteLandedBranches: true
    - match: deps/**
      parent: main
EOF
CHECKS+=(check-deps git-k8s-deps)
# Test Pods get modules only from go-cache, and the go-cache group stopped
# its upstream. go-cache now fetches from the git server's module proxy,
# which git-k8s-deps reads too, so test Pods get the versions that
# git-k8s-deps takes.
install_generated go-cache-deps
install_generated check-deps
install_generated git-k8s-deps
k -n go-cache rollout status deployment/go-cache --timeout=180s
k -n check-deps rollout status deployment/check-deps --timeout=180s
k -n git-k8s-deps rollout status deployment/git-k8s-deps --timeout=180s
# check-deps and its agent Pods fetch from the mirror, and the check pushes
# to it, as check-review does. It gets Secrets only by name, for its signing
# key.
checkdeps_sa=system:serviceaccount:check-deps:check-deps
if can_list_secrets check-deps; then
  echo "check-deps can list Secrets" >&2
  exit 1
fi
if k -n check-deps auth can-i create serviceaccounts/check-deps --subresource=token --as="${checkdeps_sa}"; then
  echo "check-deps can create tokens for its service account" >&2
  exit 1
fi
echo "check-deps can't list Secrets or create tokens."
# git-k8s-deps reads and pushes branches through the mirror, under the
# prefix that the core program gives it, and its update Pods get the
# repository's credentials from the kubelet. It gets Secrets only by name,
# for its signing key.
if can_list_secrets git-k8s-deps; then
  echo "git-k8s-deps can list Secrets" >&2
  exit 1
fi
if k -n git-k8s-deps auth can-i create serviceaccounts/git-k8s-deps --subresource=token \
  --as=system:serviceaccount:git-k8s-deps:git-k8s-deps; then
  echo "git-k8s-deps can create tokens for its service account" >&2
  exit 1
fi
echo "git-k8s-deps can't list Secrets or create tokens."
GREET_BRANCH="deps/go/example.com/greet@v1"
deps_main_requires() {
  dg fetch -q "${HOST_URL}/deps.git" main && dg show FETCH_HEAD:go.mod | grep -qx "require example.com/greet $1"
}
greet_branch_gone() { [[ -z "$(remote_head "${GREET_BRANCH}" deps)" && -z "$(branch_object "${GREET_BRANCH}" deps)" ]]; }
no_deps_pods() { [[ -z "$(k -n "${NS}" get pods -l app.kubernetes.io/name=git-k8s-deps -o name)" ]]; }

publish v1.0.1 "${long_ago}" '// Hello says hello.
func Hello() string { return "hello" }'
eventually 300 deps_main_requires v1.0.1
dg log -1 --format=%B FETCH_HEAD
dg log -1 --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Deps: go example.com/greet v1.0.1'
signed_by_git_k8s FETCH_HEAD dg
eventually 60 greet_branch_gone
eventually 60 no_deps_pods
echo "git-k8s-deps signed and pushed v1.0.1 to ${GREET_BRANCH}, which landed without approval because a patch release is low risk."

# v1.1.0 changes Hello, so the update breaks the build until the agent fixes
# the call. The proxy's time for v1.2.0 is years ahead, so it's too new to
# take.
deps_main="$(remote_head main deps)"
publish v1.1.0 "${long_ago}" 'func Hello(name string) string { return "hello, " + name }'
publish v1.2.0 2100-01-01T00:00:00Z '// Hello says hello to name.
func Hello(name string) string { return "hello, " + name }'
dep() { k -n "${NS}" get gitbranch "$(branch_object "${GREET_BRANCH}" deps)" -o jsonpath="{.status.checks.$1}"; }
fixed_and_waiting() {
  [[ -n "$(branch_object "${GREET_BRANCH}" deps)" ]] &&
    dg fetch -q "${HOST_URL}/deps.git" "refs/heads/${GREET_BRANCH}" &&
    dg log -1 --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Agent: deps' &&
    [[ "$(dep gotest.commit)" == "$(dg rev-parse FETCH_HEAD)" && "$(dep gotest.state)" == Passed ]] &&
    [[ "$(dep deps.commit)" == "$(dg rev-parse FETCH_HEAD)" && "$(dep deps.state)" == Passed ]] &&
    [[ "$(dep risk.outputs.level)" == high && "$(dep approval.state)" == Failed ]]
}
eventually 600 fixed_and_waiting
fixed="$(dg rev-parse FETCH_HEAD)"
dg log -2 --format=%B FETCH_HEAD
dg log -1 --format=%B FETCH_HEAD | grep -qx 'Git-K8s-Fixer: deps'
dg log -1 --format=%B FETCH_HEAD^ | grep -qx 'Git-K8s-Deps: go example.com/greet v1.1.0'
signed_by_git_k8s FETCH_HEAD dg
signed_by_git_k8s FETCH_HEAD^ dg
dg show FETCH_HEAD:greeting.go | grep -q 'return greet.Hello("world")$'
# Three polls later, the fix still hasn't landed.
sleep 3
[[ "$(remote_head main deps)" == "${deps_main}" ]]
# config/approved-by.yaml sets approved-by to whoever sets approve.
approver="$(k -n "${NS}" annotate gitbranch "$(branch_object "${GREET_BRANCH}" deps)" "${APPROVE}=${fixed}" \
  -o jsonpath='{.metadata.annotations.git-k8s\.imjasonh\.com/approved-by}')"
[[ "${approver}" == "${admin}" ]]
deps_landed() { [[ "$(remote_head main deps)" == "${fixed}" ]]; }
eventually 120 deps_landed
eventually 60 greet_branch_gone
eventually 60 no_deps_pods
eventually 60 no_agent_pods
# Six polls and six reconciles of git-k8s-deps later, no branch takes
# v1.2.0.
sleep 6
[[ -z "$(remote_head "${GREET_BRANCH}" deps)" ]]
deps_main_requires v1.1.0
echo "v1.1.0 broke the build, the fake agent fixed it, check-deps signed the fix, and the fix landed once ${approver} approved it. v1.2.0 is too new, so no branch takes it."

# git-k8s-deps doesn't have the approve verb, so git-k8s-approvals stops it
# from approving. The API server reports only one of the policies that deny
# a request, and not always the same one, so git-k8s-deps gets the verb here
# and names a full SHA and itself in approved-by, which leaves
# git-k8s-branches as the only policy that stops it.
deps_sa=system:serviceaccount:git-k8s-deps:git-k8s-deps
can_approve() {
  [[ "$(k -n "${NS}" auth can-i approve gitbranches.git-k8s.imjasonh.com "--as=${deps_sa}" || true)" == "$1"* ]]
}
can_approve no
k create clusterrolebinding git-k8s-e2e-deps-approve --clusterrole=git-k8s-e2e-approve \
  --serviceaccount=git-k8s-deps:git-k8s-deps
eventually 30 can_approve yes
deps_token="$(k -n git-k8s-deps create token git-k8s-deps)"
code="$(patch_branch "${deps_token}" '{}')"
[[ "${code}" == 200 ]]
for patch in "{\"metadata\":{\"annotations\":{\"${APPROVE}\":\"${fixed}\",\"${APPROVED_BY}\":\"${deps_sa}\"}}}" \
  '{"metadata":{"labels":{"e2e":"changed"}}}' "${hold}" "${reown}" "${reset}"; do
  code="$(patch_branch "${deps_token}" "${patch}")"
  cat "${WORKDIR}/patch.json"
  echo
  [[ "${code}" == 422 ]]
  grep -q "git-k8s-deps can't change GitBranch objects" "${WORKDIR}/patch.json"
done
k delete clusterrolebinding git-k8s-e2e-deps-approve
echo "git-k8s-deps can't approve a GitBranch, even with the approve verb, or change one."

can_i() { k auth can-i "$1" configmaps -n "$2" "--as=${deps_sa}" || true; }
for verb in get create patch; do
  [[ "$(can_i "${verb}" git-k8s-deps)" == yes ]]
  [[ "$(can_i "${verb}" "${NS}")" == no* ]]
done
for verb in list delete; do
  [[ "$(can_i "${verb}" git-k8s-deps)" == no* ]]
done
first_seen() { k -n git-k8s-deps get configmap git-k8s-deps-first-seen -o jsonpath='{.data.first-seen}'; }
seen_line() { grep -F "${CLUSTER_URL}/proxy example.com/greet $1 " <<<"$(first_seen)"; }
eventually 60 seen_line v1.2.0
first_seen
seen_v120="$(seen_line v1.2.0)"
k -n git-k8s-deps rollout restart deployment/git-k8s-deps
k -n git-k8s-deps rollout status deployment/git-k8s-deps --timeout=180s
publish v1.2.1 2100-01-01T00:00:00Z '// Hello says hello to name.
func Hello(name string) string { return "hello, " + name }'
eventually 120 seen_line v1.2.1
first_seen
[[ "$(seen_line v1.2.0)" == "${seen_v120}" ]]
echo "git-k8s-deps keeps when it first saw each version in a ConfigMap in its own namespace, the only one where it can read and write ConfigMaps, and kept v1.2.0's time through a restart."
echo "::endgroup::"

# The last zombie check takes 10 seconds, so it runs in the background while
# the next group waits to see that nothing writes. It reads the nodes'
# processes and writes nothing.
no_lasting_zombies >"${WORKDIR}/zombies.log" 2>&1 &
ZOMBIES_PID=$!

echo "::group::Nothing writes while nothing changes"
snapshot() {
  k -n "${NS}" get gitrepositories,gitbranches \
    -o jsonpath='{range .items[*]}{.kind}/{.metadata.name}={.metadata.resourceVersion} {end}'
  k -n git-k8s-deps get configmap git-k8s-deps-first-seen \
    -o jsonpath='{.kind}/{.metadata.name}={.metadata.resourceVersion}'
}
idle() {
  local before after
  before="$(snapshot)"
  sleep 4
  after="$(snapshot)"
  echo "resource versions: ${after}"
  [[ "${before}" == "${after}" ]]
}
eventually 60 idle
echo "Four polls of the remote wrote nothing."
echo "::endgroup::"

echo "::group::No zombie lasts, and the programs' Pods share a process namespace and meet the restricted Pod Security Standard"
zombies_status=0
wait "${ZOMBIES_PID}" || zombies_status=$?
ZOMBIES_PID=""
cat "${WORKDIR}/zombies.log"
[[ ${zombies_status} -eq 0 ]]
# generate doesn't label the programs' namespaces, so their Pods get only the
# cluster's default Pod Security level. A server-side dry run of the
# restricted label warns about each Pod that violates it. By now, CHECKS
# holds every program that the groups installed except git-k8s and go-cache.
programs=(git-k8s go-cache "${CHECKS[@]}")
for program in "${programs[@]}"; do
  shared="$(k -n "$(namespace_of "${program}")" get pods -l "app.kubernetes.io/name=${program}" \
    -o jsonpath='{range .items[*]}{.spec.shareProcessNamespace}{"\n"}{end}')"
  if [[ -z "${shared}" ]] || grep -qv '^true$' <<<"${shared}"; then
    echo "${program}'s Pods don't all share a process namespace: ${shared}" >&2
    exit 1
  fi
  k label --dry-run=server --overwrite namespace "$(namespace_of "${program}")" \
    pod-security.kubernetes.io/enforce=restricted 2>&1 >/dev/null | tee "${WORKDIR}/pod-security.log"
  if grep -q violate "${WORKDIR}/pod-security.log"; then
    echo "${program}'s Pods violate the restricted Pod Security Standard" >&2
    exit 1
  fi
done
echo "No zombie on the nodes lasted 10 seconds, and the Pods of all ${#programs[@]} programs share a process namespace and meet the restricted Pod Security Standard."
echo "::endgroup::"

echo "kind e2e passed"
