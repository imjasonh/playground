# sshcloud Terraform

First GCP environment: Firestore, GCS, Secret Manager, Artifact Registry,
**ko-built** platform images, a single SSH gateway VM, an orchestrator VM, and
a nested-virt **host MIG** running the Firecracker agent.

This is a private smoke-test environment, not a production/public module.
Public SSH is closed by default; explicitly allow only an operator/Terraform
runner `/32` while workload identity and the first operator-owned validation of
the new jailer/helper boundary remain unfinished.

## Layout

| File | What |
|------|------|
| `services.tf`, `modules/project-services/` | Required GCP API enablement barrier |
| `images.tf` | `ko_build` for platform services, VMM/TAP helpers, `guestinit`, and `fortune` |
| `demo.tf` | Optional `local-exec` join/deploy followed by strict SSH release smoke test |
| `firestore.tf` | Dedicated named Native-mode database |
| `storage.tf` | Snapshot + platform-asset buckets, Artifact Registry |
| `secrets.tf` | Gateway host key, user CA, and versioned SSH access policy |
| `gateway.tf` | Public SSH gateway (`:22`) |
| `orchestrator.tf` | Internal placement/migrate API; reloads MIG hosts file |
| `agents.tf` | Instance template + zonal MIG (`enable_nested_virtualization`) |
| `network.tf` | VPC/NAT, opt-in public `:22`, tagged internal APIs, agent SSH relay range |

`fortune` is a **sample user app image** (digest-pinned); deploy it through the
gateway — it is not a platform builtin.

## Apply

Needs: Terraform ≥ 1.6 and Go 1.25+. The applying identity must be able to
enable project services; create Compute/network, service-account, Firestore,
Storage, Secret Manager, and Artifact Registry resources; modify project IAM;
act as the created service accounts; and push Artifact Registry images.
Application Default Credentials are used by both Google and ko providers.

The module creates a dedicated Native-mode database named `sshcloud`, and
collections are further
isolated under `firestore_prefix`. This avoids collisions with an existing
`(default)` database. Conditional `roles/datastore.user` bindings restrict the
gateway and orchestrator to that exact database; the collection prefix is
additional namespace separation rather than the primary IAM boundary.

```bash
cd sshcloud
bash hack/fetch-firecracker-assets.sh
cd terraform
cp terraform.tfvars.example terraform.tfvars
# edit project_id, asset paths, a narrow ssh_client_cidrs allowlist, and
# member_ssh_public_keys / deployer_ssh_public_keys (full OpenSSH public lines)
# optionally set enable_demo_bootstrap=true

bash ../hack/preflight-gcp.sh YOUR_PROJECT us-central1 us-central1-a

terraform init
terraform plan -out=tfplan
terraform apply tfplan
```

`module.project_services` enables every required API first. API-backed
foundations and the Debian image lookup depend on that module, so a first apply
does not require a separate `gcloud services enable` bootstrap.

After apply:

```bash
# With enable_demo_bootstrap=true, Terraform waits/retries through:
# terraform_data.deploy_fortune → ssh join@ / ssh deploy@ with exec args
# terraform_data.smoke_test_fortune → strict ssh fortune@ through the release.
# Both gateway and app host keys are pinned; a bad response fails terraform apply.

# For additional manual sessions:
umask 077
terraform output -raw demo_private_key_openssh > /tmp/sshcloud-demo
terraform output -raw gateway_known_hosts > /tmp/sshcloud-known
chmod 600 /tmp/sshcloud-demo
terraform output demo_ssh
ip="$(terraform output -raw gateway_ip)"
ssh -T -p 22 -i /tmp/sshcloud-demo \
  -o IdentitiesOnly=yes \
  -o UserKnownHostsFile=/tmp/sshcloud-known \
  -o GlobalKnownHostsFile=/dev/null \
  -o StrictHostKeyChecking=yes \
  fortune@"$ip" </dev/null

# Manual deploy (when the presenting key passes deploy policy) also works:
# ssh -p 22 deploy@GATEWAY_IP \
#   fortune --image="$(terraform output -raw fortune_image)" \
#   --tier=tiny --strategy=kick --yes
```

Before testing SSH, verify the control plane:

```bash
gcloud compute instance-groups managed list-instances sshcloud-agents \
  --zone=us-central1-a
# Through an IAP/local tunnel into the VPC:
curl --fail http://ORCHESTRATOR_IP:8090/readyz
# Authenticated GET /v1/diagnostics correlates placements, capacity and inventory.
```

The operator opening an IAP tunnel needs `roles/iap.tunnelResourceAccessor`
plus OS Login/instance SSH access (for example `roles/compute.osLogin`).

Host sshd on the gateway is moved to **:2222** (IAP) so platform SSH can own `:22`.
Terraform uploads the exact local Firecracker/jailer/kernel files as
content-addressed GCS objects before creating the agent template. Agents expose gateway-reachable
SSH relays on `20000-29999`; TAP-local guest addresses are not returned across
the VPC. The fetch helper always targets the agents' `linux/x86_64`
architecture and verifies the pinned upstream release archive (both
Firecracker and matching jailer) plus kernel SHA-256 values;
it can therefore run from an ARM/macOS Terraform workstation.

The `sshcloud` agent has an empty systemd capability bounding set and cannot
open `root:kvm 0660` `/dev/kvm`. A mode-0600, SO_PEERCRED-authenticated socket
fronts the root VMM helper; its fixed capability set excludes `CAP_NET_ADMIN`,
and it launches Firecracker v1.10.1 only through the matching jailer with
per-VM UID/GID, chroot, and fixed cgroup-v2 limits. A different system user
runs the TAP helper with only `CAP_NET_ADMIN`; its RPC surface derives TAP
names/owners and constructs a fixed deny-by-default iptables/ip6tables ruleset.

**Non-interactive deploy / join** (SSH exec args, exit status set):

```bash
ssh join@HOST demo
ssh deploy@HOST fortune --image=repo@sha256:… [--tier=tiny] [--strategy=kick|drain] --yes
```

## Staged SSH-key access

Terraform always configures the gateway with a file-backed policy. Production
defaults are fail-closed: `access_join_mode = "allowlist"` and
`access_deploy_mode = "allowlist"`, with empty key lists admitting nobody.
Configure `member_ssh_public_keys` and `deployer_ssh_public_keys` with complete
OpenSSH public key lines such as `ssh-ed25519 AAAA… operator@example`, not
fingerprints or key digests. The gateway parses those lines and compares their
SHA256 fingerprints to the key presented during SSH authentication.
`authorized_keys` options are rejected rather than silently ignored.

Use the modes as three rollout stages:

1. **Private:** `allowlist` / `allowlist`. Member keys can join and use apps;
   deployer keys imply membership and can also deploy.
2. **Open membership:** `open` / `allowlist`. Any key can join and use apps,
   while only deployer keys can deploy.
3. **Self-service:** `open` / `all-users`. Any key can join, and every
   registered user can deploy.

`enable_demo_bootstrap = true` automatically adds its generated demo public key
to both policy lists. The bootstrap action depends on the policy Secret Manager
version and retries join/deploy while the gateway fetches that version.

Every policy change creates a Secret Manager version. The gateway host refreshes
`versions/latest` every minute (with up to 10 seconds of jitter), atomically
replaces the mounted JSON file, and reloads it for every admission or deploy
decision; no image rebuild or VM replacement is required. A missing, unreadable,
or corrupt configured file denies all new joins, app/menu use, and deploys.

Revocation takes effect for new admissions after the next successful refresh.
Open SSH connections are rechecked every 30 seconds and closed when their key
no longer has platform access. It does not delete the Firestore user/key record
or cancel a deploy that already passed its final authorization check. Removing
a key only from
`member_ssh_public_keys` does not revoke it while it remains a deployer,
because deployer keys imply membership. Remove it from
`deployer_ssh_public_keys` to revoke deploy, and from both lists to revoke use
in `allowlist` join mode. `join_mode = "open"` intentionally makes
membership-list removal ineffective.

## Notes

- **Keys in state:** `tls_private_key` material is in Terraform state. Fine for
  an isolated playground only. Use encrypted/locked remote state and external
  key management before any public launch.
- **Demo is opt-in:** `local-exec` is intentionally a smoke-test hack, not a
  durable application reconciler. `triggers_replace` covers its image, infra,
  scripts, deploy inputs, and access-policy version; deploy itself is same-image
  idempotent. A separate post-deploy resource verifies the released app through
  the public SSH path.
- **Internal auth:** separate interim bearer tokens protect gateway→orchestrator
  and orchestrator→agent. Source-tag firewalls and binding to each VM's VPC IP
  add defense in depth. Workload identity + mTLS remains required for launch.
- **No public default:** `ssh_client_cidrs = []` creates no public `:22` rule.
- **MIG discovery:** orchestrator `-hosts-file` is rewritten every minute from
  MIG membership (`GET /v1/hosts`).
- **Drain before host rollout:** the MIG update policy remains opportunistic so
  Terraform never kills live app VMs implicitly. From a VPC/IAP control shell,
  drain each instance before replacing it:

  ```bash
  bash ../hack/drain-agent-host.sh \
    http://ORCHESTRATOR_IP:8090 sshcloud-agent-INSTANCE \
    /secure/path/orchestrator-auth-token
  gcloud compute instance-groups managed recreate-instances sshcloud-agents \
    --instances=sshcloud-agent-INSTANCE --zone=us-central1-a
  ```

  Drain cordons the host, freezes live outer SSH sessions for a bounded window,
  bin-packs all generations onto a compatible host, commits placement, and
  reconnects the app hop. Hard auto-healing failures cannot run a pre-hook and
  still rely on durable snapshots plus lazy placement recovery.
- **One region** in v1 (`var.region` / `var.zone`).
- **Host-isolation verification still required:** CI structurally checks the
  Terraform/systemd boundary and unit-tests request/rule/argv validation, but
  cannot prove the GCE image's cgroup delegation, jailer mount/device syscalls,
  systemd ambient capability behavior, or a real cross-host jailed restore.
- Validate locally (no GCP apply): `bash hack/validate-terraform.sh`
