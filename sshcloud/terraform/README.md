# sshcloud Terraform

First GCP environment: Firestore, GCS, Secret Manager, Artifact Registry,
**ko-built** platform images, a single SSH gateway VM, an orchestrator VM, and
a nested-virt **host MIG** running the Firecracker agent.

## Layout

| File | What |
|------|------|
| `images.tf` | `ko_build` for `gateway`, `orchestrator`, `agent`, `guestinit`, `fortune`, `api` |
| `firestore.tf` | Native-mode `(default)` database |
| `storage.tf` | Snapshot + platform-asset buckets, Artifact Registry |
| `secrets.tf` | Gateway host key + user CA (tls_private_key → Secret Manager) |
| `gateway.tf` | Public SSH gateway (`:22`) |
| `orchestrator.tf` | Internal placement/migrate API; reloads MIG hosts file |
| `agents.tf` | Instance template + zonal MIG (`enable_nested_virtualization`) |
| `network.tf` | VPC, public `:22`, IAP, internal `8080`/`8090` |

The `api` image is built (scaffold stub) but not deployed as a VM.
`fortune` is a **sample user app image** (digest-pinned); deploy it through the
gateway — it is not a platform builtin.

## Apply

Needs: Terraform ≥ 1.6, `ko` provider auth to Artifact Registry (Application
Default Credentials with `artifactregistry.writer` is enough for apply from a
dev machine), Go 1.25+ on the machine running Terraform (`ko_build` compiles
locally and pushes).

```bash
cd sshcloud/terraform
cp terraform.tfvars.example terraform.tfvars
# edit project_id

terraform init
terraform apply
```

After apply:

```bash
# 1) Upload Firecracker + kernel (apps are OCI digests, not GCS rootfs blobs)
cd ..
bash hack/fetch-firecracker-assets.sh
bash hack/upload-platform-assets.sh gs://$(terraform -chdir=terraform output -raw assets_bucket)

# 2) Restart agents so they download assets
gcloud compute instance-groups managed rolling-action restart sshcloud-agents \
  --zone=us-central1-a

# 3) Join, then deploy the sample app
terraform -chdir=terraform output gateway_ssh
terraform -chdir=terraform output -raw fortune_image
# ssh -p 22 join@GATEWAY_IP
# ssh -p 22 deploy@GATEWAY_IP   # name: fortune, image: <fortune_image>
# ssh -p 22 fortune@GATEWAY_IP
```

Host sshd on the gateway is moved to **:2222** (IAP) so platform SSH can own `:22`.

## Notes

- **Keys in state:** `tls_private_key` material is in Terraform state. Fine for
  a playground; rotate before public launch.
- **MIG discovery:** orchestrator `-hosts-file` is rewritten every minute from
  MIG membership (`GET /v1/hosts`).
- **One region** in v1 (`var.region` / `var.zone`).
- Validate locally (no GCP apply): `bash hack/validate-terraform.sh`
