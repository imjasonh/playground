# sshcloud key, certificate, identity, and state rotation

This is the operator procedure for the private sshcloud prototype. It covers
the keys and identities that already exist; it does not add an issuer, an HSM,
new trust semantics, snapshot migration, or an automatic rotation controller.

## Current security boundary

Do not describe this deployment as using external key management.

Terraform currently generates and stores all of the following private material
in state:

- the public gateway's SSH host private key;
- the platform SSH user-CA signing private key;
- both HTTPS control-CA private keys (slots A and B);
- the gateway, orchestrator, agent, and snapshot control leaf private keys;
- the optional demo client's SSH private key.

Secret Manager distributes copies of those values. It does not keep them out of
Terraform state. Cloud KMS protects snapshot data and can protect the GCS state
bucket, but it does not make the Terraform-generated SSH/control keys
non-exportable. Moving issuance and signing out of Terraform remains required
before public use.

State object generations, saved plans, and operator backups can retain every
superseded Terraform-generated private key after a rotation. Disabling or
destroying a Secret Manager version does not remove those historical copies.
Protect them as key material for their full retention lifetime.

The checked-in `backend "gcs" {}` block requires an operator-supplied backend.
It does not create or secure the bucket. Each environment must complete and
verify the state migration in [Terraform state](#terraform-state) before using
these procedures.

## Invariants

1. Use a separately reviewed, saved Terraform plan with no unrelated changes.
   A saved plan contains secret values even when the terminal redacts them:
   create it on an encrypted filesystem with mode `0600`, never upload it, and
   delete it after apply.
2. Change one trust boundary at a time. Do not combine a CA, leaf, service
   account, SSH host key, user CA, access policy, and KMS rotation in one plan.
3. Add and prove new trust before removing old trust.
4. A Secret Manager version being disabled or destroyed does not revoke a key
   that was already copied. A certificate remains valid while a trusted CA and
   its other authorization factor accept it.
5. Never increment the epoch of the active control-CA slot. Never disable a
   KMS version while retained data still depends on it.
6. Stop if the inspector, mounted-file checks, authenticated control calls, or
   rollback path disagree. Do not "fix" a rotation with `terraform taint`,
   `terraform apply -replace`, broad targeting, state editing, or automatic
   destruction.
7. Keep public SSH closed except for the narrow operator `/32` needed by the
   current step. For a gateway host-key change, close it completely until every
   test client has both pins.
8. Complete the initial fortune smoke test, then set
   `enable_demo_bootstrap = false` in a separate reviewed apply before any
   rotation. Rotation plans must never rerun Terraform provisioners or retain
   the generated demo key as an unintended member/deployer credential.

## Read-only inspection

Run the cloud inventory before and after every stage:

```bash
cd sshcloud
bash hack/inspect-rotation-state.sh \
  --project PROJECT_ID \
  --region us-central1 \
  --prefix sshcloud \
  --active-ca-slot a \
  --terraform-dir terraform \
  --gateway-host GATEWAY_IP
```

It lists only:

- Secret Manager version number, state, and timestamps;
- control CA/leaf SHA-256 certificate fingerprints, validity, issuer slot, and
  exact role URI;
- SSH host/user-CA public fingerprints;
- access modes, key counts, key types, and public fingerprints;
- KMS primary and version states;
- backend type and bucket safety controls.

Secret payloads are written only to a mode-`0700` temporary directory and
removed on exit. Private keys are read only to derive a public fingerprint or
prove a cert/key pair. The scripts never invoke `terraform output -json`,
`terraform show -json`, `terraform state pull`, or `terraform state show`.
Those broad commands can reveal sensitive state.

To prove what a running role actually mounted, run
`hack/inspect-control-pki.sh` locally on that VM as an identity allowed to read
the root-owned files:

```bash
sudo bash inspect-control-pki.sh \
  --active-slot a \
  --expected-role gateway
```

For agents, inspect every current MIG instance, not one representative. Slot A
is always mounted as `ca-current.pem` and slot B as `ca-previous.pem`; those
legacy file names do not change when the signing slot changes. Both are equal
trust inputs. This fixed mapping prevents a signer flip from changing instance
startup metadata.

Record the following in the change ticket without attaching state, plans,
PEM, JSON bundles, access tokens, identity tokens, public key lines, or secret
payloads:

- plan digest and approved resource-address list;
- old/new public fingerprints and certificate expiry;
- Secret Manager version numbers and states;
- every inspected instance name and observed role/issuer fingerprint;
- control call used to prove each role;
- rollback version/fingerprint and the time rollback eligibility ends.

## Standard Terraform change protocol

```bash
cd sshcloud/terraform
umask 077
plan="$(mktemp "${TMPDIR:-/secure-volume}/sshcloud-rotation.XXXXXX.tfplan")"
terraform plan -out="$plan"
chmod 0600 "$plan"
# Review the ordinary, redacted terminal rendering. Do not use show -json.
terraform show -no-color "$plan"
sha256sum "$plan"
terraform apply "$plan"
rm -f "$plan"
```

Use an encrypted operator volume rather than `/tmp` when `/tmp` is not
encrypted. A plan that contains unexpected instance replacement, IAM removal,
secret destruction, KMS destruction, bucket changes, or another rotation must
not be applied.

Rotation inputs are monotonically increasing non-negative integers:

```hcl
control_ca_active_slot = "a"
control_ca_rotation_epochs = {
  a = 0
  b = 1
}
control_leaf_rotation_epochs = {
  gateway      = 0
  orchestrator = 0
  agent        = 0
  snapshot     = 0
}
gateway_host_key_rotation_epoch = 0
```

Epochs are the operator-controlled replacement trigger. Setting
`early_renewal_hours = 0` disables pre-expiry renewal, but the TLS provider
will still propose certificate replacement at hard expiry. Never run
unattended applies: rotate through this procedure before expiry, and reject any
certificate replacement not caused by the reviewed epoch or signer change.
Epoch zero has `moved` mappings from the pre-epoch resource addresses, so
adopting this configuration with all defaults at zero must preserve existing
keys and certificates. The first plan may update only the old early-renewal
metadata to zero in place; stop if it proposes certificate/key replacement.
Superseded Secret Manager versions use `deletion_policy = "ABANDON"` and remain
for the manual cleanup procedure. An epoch is not a schedule and must never be
incremented by unattended dependency automation.

## Staged control-CA A/B rotation

The example starts with A signing and both A/B trusted. Reverse A and B on the
next cycle.

### Stage 0: establish the baseline

1. Confirm `control_ca_active_slot = "a"` in the applied state-specific inputs.
2. Run both inspectors. Every role leaf must have the expected URI and
   `issuer_slot=a`; every role must mount the same A and B fingerprints.
3. Confirm both CA latest versions are `ENABLED` and valid for more than 30
   days. Confirm role leaves will not expire during the change.
4. Force and verify one normal refresh on every role:

   ```bash
   sudo systemctl start sshcloud-control-identity-refresh.service
   sudo systemctl is-active sshcloud-control-identity-refresh.timer
   ```

5. Record a working authenticated path for each edge:
   gateway→orchestrator, orchestrator→agent, orchestrator→gateway migration,
   and agent→snapshotd. Health endpoints are not proof: they are deliberately
   unauthenticated and non-diagnostic.

### Stage 1: replace only idle CA B

1. Increment only `control_ca_rotation_epochs.b`.
2. The plan may replace only:
   the old/new epoch-addressed `tls_private_key.control_ca["b-N"]`,
   `tls_self_signed_cert.control_ca["b"]`, and
   `google_secret_manager_secret_version.control_ca["b"]`.
   It must not reissue leaves or replace/update Compute resources.
3. Apply, then wait at least one refresh interval plus jitter (70 seconds), or
   explicitly start the refresh service on every role.
4. Inspect Secret Manager and every mounted role. All must still show the old A
   fingerprint as active and the same new B fingerprint as standby.
5. Exercise every authenticated edge while leaves still chain to A. This proves
   that distributing B did not remove A.

Do not continue if any instance has the old B, lacks A, or cannot make its
normal authenticated request.

### Stage 2: issue leaves under B

1. Change only `control_ca_active_slot` from `a` to `b`. Do not change either CA
   epoch and do not change leaf epochs in this apply.
2. The plan should reissue the four
   `tls_locally_signed_cert.control_role` resources and create four control
   identity secret versions. Private leaf keys remain unchanged. Because trust
   slots are fixed A/B, no Compute instance or agent template should change.
3. Apply. Refresh one role at a time in this order, proving its relevant edge
   before continuing:
   snapshot, agent, orchestrator, gateway. This order moves servers before the
   callers most directly dependent on them while A remains trusted everywhere.
4. For each role:
   - record its process/container start time;
   - start `sshcloud-control-identity-refresh.service`;
   - use the live inspector to require the same URI, a matching key, and
     `issuer_slot=b`;
   - repeat the authenticated operation;
   - prove the process/container start time did not change.

The TLS implementation rereads leaf, key, A, and B on each new handshake.
Control HTTP clients disable keep-alives, so the authenticated operation must
show the new leaf without a process restart.

### Stage 3: prove A is idle, then refresh it

1. Enumerate every gateway, orchestrator, snapshot, and current agent instance.
   Every mounted leaf must chain only to B. Include powered-on replacement or
   repair instances; do not rely only on the MIG target count.
2. Wait until any in-flight request that began with an A leaf has completed.
   Long snapshot/agent operations can last up to 20 minutes and orchestrator
   operations longer; use the actual operation inventory, not a fixed sleep.
3. Increment only `control_ca_rotation_epochs.a`.
4. The plan must match the four-resource idle-slot shape from Stage 1, with A
   in place of B. Apply and distribute new A to every role.
5. Prove B-signed control calls still work, then retain old A's abandoned
   Secret Manager version for the rollback window before cleanup.

The resulting steady state is B signing, with B + fresh A trusted. The next
rotation is B→A: replace idle A, sign leaves with A, prove B idle, then replace
B.

### CA rollback and compromise

- Before Stage 2, rollback means republishing the prior B certificate as a new
  Secret Manager version and refreshing every role. Disabling the latest
  version is not rollback: Secret Manager's `latest` alias does not fall back
  to an older enabled version. That emergency version is Terraform drift;
  after recovery, increment the still-idle B epoch in a reviewed plan to
  reconcile the managed latest version.
- During Stage 2, both CAs remain trusted. Revert
  `control_ca_active_slot`, apply new leaf versions under A, refresh, and prove
  all edges.
- Never destroy the old CA version during the change.
- If one CA private key is suspected compromised, stop issuing with it, move
  every leaf to the clean slot, prove no old leaf remains, replace the
  compromised slot, and consider the independent GCE identity factor.
- If Terraform state exposed both CA private keys, ordinary A/B overlap is not
  a safe trust bridge. Close ingress and control mutations, preserve evidence,
  create clean roots and leaves through an approved recovery change, replace
  trust on all roles in a coordinated maintenance window, and reject both old
  roots. Do not let a compromised root authenticate the recovery.

## Control role leaf key/certificate rotation

Rotate one role per apply. Increment only that role in
`control_leaf_rotation_epochs`.

Expected plan:

- one old/new epoch-addressed role private key plus its CSR and locally signed
  certificate;
- one role control-identity Secret Manager version;
- no CA, Compute, IAM, network, KMS, bucket, or other role change.

Procedure:

1. Verify the active CA has enough remaining validity for the new leaf's full
   intended lifetime. Rotate the inactive/active CAs first if needed.
2. Apply the one-role plan.
3. Refresh every instance of that role. The agent leaf is shared by all MIG
   members, so every member must report the new fingerprint.
4. Require the exact URI:
   - `spiffe://sshcloud.internal/control/gateway`
   - `spiffe://sshcloud.internal/control/orchestrator`
   - `spiffe://sshcloud.internal/control/agent`
   - `spiffe://sshcloud.internal/control/snapshot`
5. Require `key_match=yes`, the configured active issuer slot, and unchanged
   A/B trust fingerprints.
6. Prove dynamic reload without restart and exercise both directions in which
   the role participates. Rotate the next role only after this passes.
7. Retain the old secret version through the rollback window, then follow
   Secret Manager cleanup.

Disabling the old identity secret version prevents a future fetch but does not
revoke a copied old private key. The old certificate remains accepted until it
expires or its issuing CA is removed. mTLS is only one factor: production
requests also need an audience-bound GCE identity token for the exact expected
service-account email and project/instance claims.

## GCE service-account replacement

There are no user-managed Google service-account keys in the intended design.
Workloads fetch identity tokens and OAuth access tokens from GCE metadata.
Creating a JSON service-account key is not rotation and is prohibited.

The server currently accepts exactly one service-account email per caller
role; it has no dual-email overlap. Terraform also declares fixed account IDs.
Therefore service-account replacement is a coordinated maintenance change, not
an epoch bump. Do not delete and recreate the same account ID: IAM bindings are
tied to the deleted principal's unique identity, and same-email reuse also
leaves already minted tokens ambiguous.

Identity-token facts:

- a fresh token is requested from metadata for each control request, but Google
  may return a cached token;
- verification allows Google's normal token lifetime, bounded to 65 minutes
  plus 30 seconds of skew in the current code;
- tokens bind exact audience, email, project ID/number, and full GCE instance
  claims; snapshot authorization additionally binds exact instance name/ID;
- revoking IAM or deleting a service account does not retroactively erase an
  already minted token;
- changing the verifier's expected email rejects the old email immediately,
  but the role certificate remains a separate required factor.

Replacement procedure for one role:

1. Inventory all IAM grants, secret grants, bucket/KMS grants, Artifact Registry
   access, attached instances/templates, and peer configurations for the old
   email. Check that the old account has no user-managed keys.
2. Create a new account with a new email in a reviewed Terraform change. Grant
   only the old role's required permissions; do not remove the old grants yet.
3. Update every verifier that expects this caller and the caller's attached
   service account in one maintenance plan. Because only one email is accepted,
   a temporary control outage is expected. Drain/stop affected work before
   apply.
4. Recreate or restart the caller instances as required for the new attached
   account. Metadata tokens cannot be switched by changing a file.
5. Verify the new email and immutable instance claims on every authenticated
   edge, then ensure all old instances are stopped.
6. Change peers to accept only the new email if that was not atomic. Wait at
   least 65 minutes plus skew before treating old tokens as expired.
7. Remove the old account's IAM grants, disable it, observe the rollback window,
   then delete it under the organization's principal-retention policy.

Peer dependencies:

| Caller being replaced | Verifiers/configuration that must move |
|---|---|
| gateway | orchestrator gateway listener |
| orchestrator | agent, gateway migration listener, and orchestrator local admin verifier |
| agent | snapshotd; every agent template/instance must attach the new account |
| snapshot | no current outbound control peer, but its GCS/KMS/Firestore and secret grants plus VM attachment must move |

Do not combine service-account replacement with CA/leaf rotation. If the old
workload is compromised, close the affected control edge first; overlap is for
availability, not a reason to keep a hostile identity accepted.

## Member and deployer SSH access keys

The policy secret contains public keys only, but it is versioned and distributed
through the same fail-closed path. Deployer keys imply membership.

### Add

1. Obtain the full OpenSSH public line through an authenticated operator
   channel and verify its SHA-256 fingerprint with the owner out of band.
2. Add it to `member_ssh_public_keys`, `deployer_ssh_public_keys`, or both.
3. Apply only the access-policy Secret Manager version.
4. Run the inspector; it prints fingerprints, never key bodies/comments.
5. Force refresh if needed:

   ```bash
   sudo systemctl start sshcloud-access-policy-refresh.service
   ```

6. Prove the new key's least privilege. A member must not deploy; a deployer
   must first be a registered user even though it implies membership.

### Revoke and cut off active connections

1. In `allowlist` join mode, remove a key from both member and deployer lists to
   revoke platform use. Removing it only from members does nothing while it is
   a deployer.
2. With `deploy_mode = "allowlist"`, to revoke deploy but preserve use, remove
   it only from deployers and retain it as a member.
3. With `deploy_mode = "all-users"`, deployer-list removal cannot revoke deploy
   from a registered user by design. Move to the allowlist mode before claiming
   selective deploy revocation.
4. In `join_mode = "open"`, member-list removal cannot revoke platform use by
   design. Move to an allowlist or close ingress before claiming revocation.
5. Apply and inspect the new policy version.
6. The normal worst-case cutoff after a successful fetch is approximately 100
   seconds: up to 60 seconds plus 10 seconds refresh jitter, then the gateway's
   30-second open-connection recheck. A failed refresh removes the policy file
   and fails new decisions closed; confirm the service succeeded.
7. For deterministic cutoff, start the refresh service, wait one 30-second
   recheck, and prove the old connection closes. If immediate emergency cutoff
   is required, close public ingress or restart the gateway container, which
   disconnects every user, not just the revoked key.

Revocation does not erase the Firestore user/key registration and cannot undo a
deploy mutation that passed its final authorization check before the refresh.
Investigate and reconcile such a deploy separately.

## Gateway SSH host-key rotation

Clients pin the platform gateway host key. The platform process loads one key
at startup and does not dynamically reload it. A safe change therefore uses a
planned public-SSH maintenance window.

1. Record the old live fingerprint and exact old `known_hosts` entry. Verify it
   against the current `rotation_status` output and inspector.
2. Set `ssh_client_cidrs = []` in a separate plan/apply. Existing clients must
   be notified before this outage. Keep IAP/OS Login host administration on
   sshd port 2222 available.
3. Increment only `gateway_host_key_rotation_epoch`. The plan may replace the
   old/new epoch-addressed `tls_private_key.gateway_host` instance and the
   gateway-host Secret Manager version, and update non-sensitive outputs. It
   must not replace the gateway VM. Apply while public SSH remains closed.
4. Obtain the new public entry with the specific output only:

   ```bash
   terraform output -raw gateway_known_hosts
   terraform output -json rotation_status
   ```

   Never run broad `terraform output -json`; it would include the sensitive
   optional demo private-key output.
5. Distribute an atomic `known_hosts` file containing both old and new entries
   for the same endpoint. Verify the file on every test client. Do not use
   `StrictHostKeyChecking=accept-new`, `ssh-keyscan` as trust, or
   `UserKnownHostsFile=/dev/null`. `ssh-keyscan` is useful only to compare the
   live presentation with an already authenticated expected fingerprint.
6. Reset/reboot the gateway VM in the maintenance window so its startup script
   fetches the new latest secret, then use the inspector to compare the live
   Ed25519 fingerprint. Restarting only the container is insufficient because
   it would reread the old host file.
7. Restore only the approved `/32` ingress and verify strict clients.
8. Keep both pins and the abandoned old secret version for the rollback window.
   Then remove the old pin from clients before disabling/destroying the old
   version.

Rollback requires republishing the old secret payload as a new version, resetting
the gateway, and retaining the old pin. Copy an old version only through
mode-`0600` temporary files; do not print it:

```bash
umask 077
tmp="$(mktemp)"
gcloud secrets versions access OLD_VERSION \
  --secret=sshcloud-gateway-host-key \
  --project=PROJECT_ID \
  --out-file="$tmp"
gcloud secrets versions add sshcloud-gateway-host-key \
  --project=PROJECT_ID \
  --data-file="$tmp"
rm -f "$tmp"
```

That emergency version is outside Terraform state. After recovery, perform a
new reviewed epoch rotation to reconcile the Terraform-managed latest key.

## Platform SSH user-CA rotation

This is distinct from the HTTPS control CAs. The gateway signs short-lived user
certificates; each app generation trusts the public CA injected into its
rootfs.

The current platform has one signer and injects one public key. The sample
`fortune` app parses exactly one CA, sleeping snapshots retain their injected
rootfs, and there is no Terraform user-CA A/B epoch. Consequently a no-downtime
user-CA rotation is **not currently executable**. Do not bump/replace the
single Terraform key and claim success: new and existing app generations would
split trust.

Required gated procedure:

1. Inventory every active, draining, and sleeping app generation.
2. Prepare a next CA in an approved signing system and distribute only its
   public key. Do not switch the gateway signer.
3. Make each app capable of trusting old + next simultaneously. Deploy a new
   generation for every app, and replace rather than restore sleeping
   generations whose rootfs contains only the old CA. The present sample app
   must be changed before this gate can pass.
4. Prove every generation still accepts an old-CA user certificate and has the
   authenticated next public fingerprint.
5. In a maintenance change, switch the gateway signer to the next private key.
   The current Terraform layout needs reviewed dual-slot/signing integration
   before this step; manual `taint`/`-replace` is prohibited.
6. Prove a newly minted certificate works against every app generation.
7. Wait longer than the maximum user-certificate TTL (currently five minutes)
   and drain pre-switch sessions.
8. Deploy app generations trusting only the new CA. Remove/expire all snapshots
   and old generations that retain old trust.
9. Only then disable and later destroy the old signing-key secret version.

If the old user-CA private key is compromised, old certificates can be minted
until old trust is removed. Close ingress and use a coordinated all-app
maintenance rollout; Secret Manager disable alone is not revocation.

## Snapshot envelope KEK and bucket CMEK versions

The two Cloud KMS keys have different dependencies:

- `snapshot-envelope` wraps each snapshot's fresh streaming-AEAD keyset.
  Ciphertexts already wrapped by version N still require version N for restore.
  There is currently no rewrap tool.
- `snapshot-bucket` is the GCS default CMEK. Changing its primary affects new
  writes only. Every retained object generation encrypted with version N still
  requires N unless it is rewritten or deleted.

Terraform sets no automatic KMS rotation schedule. Rotate one key at a time:

1. Run the inspector and inventory every `ENABLED`, primary, scheduled, and
   destroyed version. Preserve the snapshot/object retention inventory outside
   Terraform.
2. Create a new key version:

   ```bash
   gcloud kms keys versions create \
     --key=snapshot-envelope \
     --keyring=sshcloud-snapshots \
     --location=REGION \
     --project=PROJECT_ID
   ```

3. Confirm the new version is `ENABLED`, then explicitly set it primary:

   ```bash
   gcloud kms keys set-primary-version snapshot-envelope \
     --version=NEW_VERSION \
     --keyring=sshcloud-snapshots \
     --location=REGION \
     --project=PROJECT_ID
   ```

4. Create a new snapshot and prove, from metadata/a controlled restore, that a
   new write uses the new primary. This runbook does not add or change the
   snapshot data path.
5. For the envelope KEK, keep every old version enabled until every snapshot
   package wrapped by it has expired/deleted or a future rewrap process has
   migrated it. Today that can mean retaining the old version indefinitely.
6. For bucket CMEK, set the new bucket-key version primary, prove new object
   generations use it, then inventory **all current and noncurrent GCS object
   generations**. GCS does not automatically reencrypt existing objects.
   Rewrite or expire all old-version generations under a separately reviewed
   data migration before considering disable. Do not treat changing the bucket
   default as migration.
7. When dependency inventory is empty, disable (do not destroy) the old version:

   ```bash
   gcloud kms keys versions disable OLD_VERSION \
     --key=KEY_NAME \
     --keyring=sshcloud-snapshots \
     --location=REGION \
     --project=PROJECT_ID
   ```

8. Run restore/read drills across the full retention set. If any dependency was
   missed, re-enable immediately.
9. Keep the disabled version for the approved rollback/retention period. Then
   schedule destruction with `gcloud kms keys versions destroy`. That command
   enters `DESTROY_SCHEDULED`; it does not immediately erase key material.
   Review the KMS destruction delay and inventory again, and restore the version
   before the deadline if anything is uncertain.
10. Allow scheduled destruction to complete only when no legal, backup, object
    version, snapshot, rollback, or incident-response dependency remains.

Ordering is always:

`create → enable/verify → set primary → prove new writes → migrate/expire all
dependencies → disable → restore/read drill → wait → schedule destroy → destroy`

Never disable/destroy the primary first. Never rotate both keys in one change.
KMS key resources have Terraform `prevent_destroy`; do not remove it.

## Secret Manager version cleanup

`ABANDON` prevents Terraform replacement from disabling/destroying the previous
version. Cleanup is an explicit operation after a successful rotation.

For each secret:

1. List versions and record the latest version number. Do not assume `latest`
   falls back when disabled; it refers to the highest version number.
2. Map every consumer and mounted fingerprint. For control identity/CA secrets,
   inspect every role/agent. For host/user keys, account for clients and app
   generations. For access policy, retain at least one known-good rollback
   policy.
3. Confirm rollback can be performed by copying the old payload into a **new**
   version without printing it. A manually added rollback version is Terraform
   drift and must be reconciled by the next approved epoch/content change.
4. Disable the old numbered version:

   ```bash
   gcloud secrets versions disable OLD_VERSION \
     --secret=SECRET_ID \
     --project=PROJECT_ID
   ```

5. Run the normal operation and refresh drill. Re-enable the numbered version
   if rollback requires its payload.
6. Wait through the secret-specific retention and incident-response period.
7. Destroy the numbered version only after copied-key/certificate validity and
   rollback requirements have ended:

   ```bash
   gcloud secrets versions destroy OLD_VERSION \
     --secret=SECRET_ID \
     --project=PROJECT_ID
   ```

Destroy is irreversible and is not cryptographic revocation. For a compromised
key, rotate the accepting trust/identity and contain the workload before
cleanup. Cleanup also does not erase the same private key from historical
Terraform state generations, saved plans, or backups.

## Terraform state

### Backend bootstrap and migration

The GCS backend bucket must be administered outside this state; a stack cannot
safely own the bucket that is required to read and destroy itself. Required
controls:

- dedicated bucket and prefix per environment;
- uniform bucket-level access and public-access prevention;
- object versioning plus soft delete or a retention policy;
- Google-managed encryption at minimum, preferably a separately administered
  CMEK with narrowly scoped encrypter/decrypter access;
- no `allUsers`/`allAuthenticatedUsers`, no legacy object ACL workflow;
- a dedicated Terraform runner identity with only required bucket/prefix and
  KMS access; human access through audited break-glass;
- native backend locking, with force-unlock only after proving the holder dead;
- access logs/audit retention under the organization's security policy.

Do not put access tokens, JSON credentials, or customer-supplied encryption key
bytes in backend HCL. Use ADC/workload identity. Copy
`backend.gcs.hcl.example` to the git-ignored `backend.gcs.hcl`.

Freeze applies, then make a private pre-migration backup:

```bash
cd sshcloud/terraform
umask 077
backup="/encrypted/operator-volume/terraform-$(date -u +%Y%m%dT%H%M%SZ).tfstate"
if [[ -f terraform.tfstate ]]; then
  # The new backend block may require init before `state pull`; copy the
  # current local state directly before asking Terraform to migrate it.
  install -m 0600 terraform.tfstate "$backup"
else
  terraform state pull >"$backup"
fi
chmod 0600 "$backup"
sha256sum "$backup" >"$backup.sha256"
jq '{lineage, serial, terraform_version}' "$backup"
```

`state pull` writes every private key. It must always be redirected; never let
it print to a terminal or CI log.

Migrate:

```bash
cp backend.gcs.hcl.example backend.gcs.hcl
chmod 0600 backend.gcs.hcl
# Edit bucket/prefix only; use ambient credentials.
terraform init -migrate-state -backend-config=backend.gcs.hcl
bash ../hack/inspect-terraform-backend.sh \
  --terraform-dir "$PWD" \
  --project=PROJECT_ID
```

Pull a post-migration backup to the encrypted volume and compare only lineage,
serial, and a `terraform state list` resource-address inventory. Do not diff
raw state in tickets/CI. After verification, remove local `.tfstate` and plan
copies according to encrypted-media policy; ordinary deletion is not a
guaranteed secure erase on SSDs/snapshots.

### Backup and restore

- Treat every state object generation and local backup as a production secret.
- Periodically test listing object generations and restoring a selected
  generation into an isolated, access-controlled recovery prefix.
- Never overwrite the live state while another apply/lock exists.
- Before `terraform state push`, verify lineage/serial, stop all writers,
  preserve the current remote generation, obtain two-person review, and use
  the exact recovery artifact. A wrong push can orphan infrastructure and
  publish old private keys as current.
- Do not use `-force` to bypass lineage/serial protections as routine recovery.
- Never delete the backend bucket/key in the sshcloud destroy plan.

### Access review

The backend inspector reports controls and IAM binding counts, not member names.
Review the actual bucket policy and inherited project/folder/organization roles
in the restricted operator channel; bucket IAM alone cannot prove that inherited
access is absent. Remove broad Storage Admin/Owner grants, stale humans/runners,
credential files, and public bindings. KMS decrypt access to a state CMEK is as
sensitive as bucket object read access; review both together.

### State-exposure incident response

1. Stop applies and preserve the backend generation, lock metadata, IAM/audit
   evidence, and hashes. Do not destroy evidence or force-unlock an active run.
2. Remove the suspected reader/writer, revoke its credentials, and move state
   operations to a clean runner. Keep an audited break-glass path.
3. Assume every Terraform-held private key listed at the top of this runbook is
   copied. Secret Manager cleanup alone is insufficient because state contains
   the originals.
4. Close public ingress and restrict control operations while rotating:
   - gateway host key and client pins;
   - platform user CA through the all-app dual-trust gate;
   - both control roots and every leaf through a clean-root maintenance
     recovery (normal overlap is unsafe if both roots leaked);
   - optional demo client key and any access-list entry that trusts it.
5. Review service-account IAM/attachments and all user-managed keys. GCP KMS
   key material is non-exportable and not present in state, so do not destroy
   snapshot KMS versions merely because state leaked; review unauthorized KMS
   use and rotate versions only according to data dependencies.
6. Write recovered state to a new backend prefix/bucket with clean access,
   preserve the compromised generation under incident retention, reinitialize,
   and compare lineage/resource addresses.
7. Reopen control edges and public SSH only after strict fingerprint,
   authenticated-edge, and least-privilege checks pass.

## Completion record

A rotation is complete only when:

- the intended epoch/primary/version is recorded;
- every consumer presents or trusts the intended fingerprint;
- exact role URI and independent GCE identity checks still pass;
- strict SSH pins work without permissive client options;
- old dependencies are inventoried and retained or retired in order;
- rollback was proved without printing secret material;
- Terraform state/backend inspection passes;
- no claim is made that a documented procedure is an executed production
  drill or that Terraform-held keys are externally managed.
