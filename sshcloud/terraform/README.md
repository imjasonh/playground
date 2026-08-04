# sshcloud Terraform

First GCP environment: Firestore, GCS, Secret Manager, Artifact Registry,
**ko-built** platform images, a single SSH gateway VM, an orchestrator VM, and
a nested-virt **host MIG** running the Firecracker agent.

This is a private smoke-test environment, not a production/public module.
Public SSH is closed by default; explicitly allow only an operator/Terraform
runner `/32` while quotas and abuse controls remain unfinished.

## Layout

| File | What |
|------|------|
| `images.tf` | `ko_build` for `gateway`, `orchestrator`, `agent`, `guestinit`, `fortune`, `api` |
| `demo.tf` | Optional bootstrap user + `local-exec` `ssh deploy@… --image=…` smoke test |
| `firestore.tf` | Native-mode `(default)` database |
| `storage.tf` | Snapshot + platform-asset buckets, Artifact Registry |
| `secrets.tf` | Gateway host key + user CA (tls_private_key → Secret Manager) |
| `gateway.tf` | Public SSH gateway (`:22`) |
| `orchestrator.tf` | Internal placement/migrate API; reloads MIG hosts file |
| `agents.tf` | Instance template + zonal MIG (`enable_nested_virtualization`) |
| `network.tf` | VPC/NAT, opt-in public `:22`, tagged internal APIs, agent SSH relay range |

The `api` image is built (scaffold stub) but not deployed as a VM.
`fortune` is a **sample user app image** (digest-pinned); deploy it through the
gateway — it is not a platform builtin.

## Apply

Needs: Terraform ≥ 1.6, `ko` provider auth to Artifact Registry (Application
Default Credentials with `artifactregistry.writer` is enough for apply from a
dev machine), Go 1.25+ on the machine running Terraform (`ko_build` compiles
locally and pushes).

```bash
cd sshcloud
bash hack/fetch-firecracker-assets.sh
cd terraform
cp terraform.tfvars.example terraform.tfvars
# edit project_id, asset paths, and a narrow ssh_client_cidrs allowlist
# optionally set enable_demo_bootstrap=true

terraform init
terraform apply
```

After apply:

```bash
# With enable_demo_bootstrap=true, Terraform waits/retries through:
# terraform_data.deploy_fortune → ssh join@ / ssh deploy@ with exec args.
terraform -chdir=terraform output -raw demo_private_key_openssh > /tmp/sshcloud-demo
chmod 600 /tmp/sshcloud-demo
terraform -chdir=terraform output demo_ssh
# ssh -p 22 -i /tmp/sshcloud-demo fortune@GATEWAY_IP

# Manual deploy (any joined user) also works non-interactively:
# ssh -p 22 deploy@GATEWAY_IP \
#   fortune --image="$(terraform -chdir=terraform output -raw fortune_image)" \
#   --tier=tiny --strategy=kick --yes
```

Host sshd on the gateway is moved to **:2222** (IAP) so platform SSH can own `:22`.
Terraform uploads the exact local Firecracker/kernel files as content-addressed
GCS objects before creating the agent template. Agents expose gateway-reachable
SSH relays on `20000-29999`; TAP-local guest addresses are not returned across
the VPC.

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
  script, and deploy inputs; deploy itself is same-image idempotent.
- **Internal auth:** separate interim bearer tokens protect gateway→orchestrator
  and orchestrator→agent. Source-tag firewalls and binding to each VM's VPC IP
  add defense in depth. Workload identity + mTLS remains required for launch.
- **No public default:** `ssh_client_cidrs = []` creates no public `:22` rule.
- **MIG discovery:** orchestrator `-hosts-file` is rewritten every minute from
  MIG membership (`GET /v1/hosts`).
- **No automatic host rollout:** the MIG update policy is opportunistic until
  termination-aware host drain exists. Template changes do not justify killing
  live app VMs; apply a controlled replacement only during private smoke tests.
- **One region** in v1 (`var.region` / `var.zone`).
- Validate locally (no GCP apply): `bash hack/validate-terraform.sh`
