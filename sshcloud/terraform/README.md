# sshcloud Terraform

First GCP environment: Firestore, GCS, Secret Manager, Artifact Registry,
**ko-built** platform images, a single SSH gateway VM, an orchestrator VM, and
a nested-virt **host MIG** running the Firecracker agent.

This is a private smoke-test environment, not a production/public module.
Public SSH is closed by default; explicitly allow only an operator/Terraform
runner `/32` while the VMM jailer and workload identity remain unfinished.

## Layout

| File | What |
|------|------|
| `services.tf`, `modules/project-services/` | Required GCP API enablement barrier |
| `images.tf` | `ko_build` for `gateway`, `orchestrator`, `agent`, `guestinit`, `fortune` |
| `demo.tf` | Optional `local-exec` join/deploy followed by strict SSH release smoke test |
| `firestore.tf` | Dedicated named Native-mode database |
| `storage.tf` | Snapshot + platform-asset buckets, Artifact Registry |
| `secrets.tf` | Gateway host key + user CA (tls_private_key → Secret Manager) |
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
# edit project_id, asset paths, and a narrow ssh_client_cidrs allowlist
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

# Manual deploy (any joined user) also works non-interactively:
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
Terraform uploads the exact local Firecracker/kernel files as content-addressed
GCS objects before creating the agent template. Agents expose gateway-reachable
SSH relays on `20000-29999`; TAP-local guest addresses are not returned across
the VPC. The fetch helper always targets the agents' `linux/x86_64`
architecture and verifies pinned upstream Firecracker and kernel SHA-256 values;
it can therefore run from an ARM/macOS Terraform workstation.

**Non-interactive deploy / join** (SSH exec args, exit status set):

```bash
ssh join@HOST demo
ssh deploy@HOST fortune --image=repo@sha256:… [--tier=tiny] [--strategy=kick|drain] --yes
```

## Notes

- **Keys in state:** `tls_private_key` material is in Terraform state. Fine for
  an isolated playground only. Use encrypted/locked remote state and external
  key management before any public launch.
- **Demo is opt-in:** `local-exec` is intentionally a smoke-test hack, not a
  durable application reconciler. `triggers_replace` covers its image, infra,
  scripts, and deploy inputs; deploy itself is same-image idempotent. A separate
  post-deploy resource verifies the released app through the public SSH path.
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
- Validate locally (no GCP apply): `bash hack/validate-terraform.sh`
