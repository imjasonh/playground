#!/usr/bin/env bash
# Fail the Deploy GCP workflow unless the jobs that this event requires
# actually ran. A skipped job is a successful workflow, so this is what
# turns "the check never started" into a failure.
#
# Env:
#   PREPARE     needs.prepare.result
#   CHECK       needs.check.result
#   DEPLOY      needs.deploy.result
#   APPS        needs.prepare.outputs.apps, a JSON array
#   EVENT_NAME  github.event_name
#   REF         github.ref
#
# Nothing to deploy: prepare succeeded, and check and deploy were skipped.
# A selected app: check succeeded. Apply then depends on the event.
#   pull_request       deploy skipped
#   push or dispatch on main    deploy succeeded
#   push or dispatch off main   deploy failed the main-branch check
set -euo pipefail

fail() {
  echo "::error::$*" >&2
  exit 1
}

: "${PREPARE:?PREPARE must be set}"
: "${CHECK:?CHECK must be set}"
: "${DEPLOY:?DEPLOY must be set}"
: "${APPS?APPS must be set}"
: "${EVENT_NAME:?EVENT_NAME must be set}"
: "${REF:?REF must be set}"

if [[ "$PREPARE" != "success" ]]; then
  fail "prepare ${PREPARE}"
fi
if [[ -z "$APPS" ]]; then
  fail "prepare did not set apps"
fi

if [[ "$APPS" == "[]" ]]; then
  [[ "$CHECK" == "skipped" ]] || fail "check was ${CHECK} with no apps selected"
  [[ "$DEPLOY" == "skipped" ]] || fail "deploy was ${DEPLOY} with no apps selected"
  echo "No GCP apps selected."
  exit 0
fi

if [[ "$CHECK" != "success" ]]; then
  fail "check ${CHECK}. The GitHub environment for each selected app needs GCP_PROJECT_ID, GCP_WORKLOAD_IDENTITY_PROVIDER, GCP_DEPLOY_SERVICE_ACCOUNT, and GCP_TF_STATE_BUCKET."
fi

if [[ "$EVENT_NAME" == "pull_request" ]]; then
  [[ "$DEPLOY" == "skipped" ]] || fail "deploy was ${DEPLOY} on a pull request"
  echo "Configuration check passed. Apply runs on main."
  exit 0
fi

if [[ "$EVENT_NAME" != "push" && "$EVENT_NAME" != "workflow_dispatch" ]]; then
  fail "unexpected event ${EVENT_NAME}"
fi

if [[ "$REF" == "refs/heads/main" ]]; then
  [[ "$DEPLOY" == "success" ]] || fail "deploy ${DEPLOY}"
  echo "Applied on main."
  exit 0
fi

# Off main, the deploy job must run and reject the ref. A skip would be a
# green workflow that did not apply.
[[ "$DEPLOY" == "failure" ]] || fail "deploy off main was ${DEPLOY}. Expected the main-branch check to fail the job."
echo "Refused to apply off main."
