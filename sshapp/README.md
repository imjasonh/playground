# sshapp — SSH apps on GKE Autopilot

`sshapp` runs Wish (SSH) apps on a GKE Autopilot cluster and publishes each one
at `<app>.<domain>` on port 22. There is no HTTP ingress. Terraform builds
images with [`ko_build`](https://registry.terraform.io/providers/ko-build/ko),
deploys them, and writes Cloud DNS A records to each Service LoadBalancer IP.

## Layout

```
sshapp/
├── apps/
│   └── hello/          # example Wish app (Go)
├── terraform/
│   ├── modules/ssh_app/  # reusable ko_build + Deployment + Service + DNS
│   └── *.tf
├── go.mod
└── README.md
```

To add another app:

1. Create `apps/<name>/` with a `main` package (Wish server on `:2222`).
2. Add an entry to `var.apps` in Terraform (see `terraform.tfvars.example`).
3. Apply. Terraform builds with `ko_build`, deploys, and creates `<name>.<domain>`.

## Security model

- **Autopilot + private nodes.** Nodes have no public IPs. Egress uses Cloud NAT.
  Private Google Access covers Artifact Registry pulls.
- **SSH only.** Each app is a TCP LoadBalancer on port 22 targeting container
  port 2222. No Ingress, Gateway, or HTTP Service.
- **Source ranges.** Set `ssh_allowed_cidrs` so the LoadBalancers are not open
  to the whole Internet unless you intend that.
- **Stable host keys.** Terraform generates an ED25519 host key per app, stores
  it in a Kubernetes Secret, and injects it into the pod so clients see a stable
  fingerprint across rollouts.
- **Locked-down pods.** Non-root, read-only root filesystem, all capabilities
  dropped, no service-account token mount.
- **Public-key auth only.** The hello app accepts any public key (demo behavior)
  and never enables password auth. Tighten that per app before production use.
- **Workload Identity Federation for GitHub Actions.** Set `github_repository`
  when you are ready; Terraform creates the WIF pool, provider, and deploy SA.
  Leave it empty for the first bring-up.

DNS for SSH cannot share one IP the way HTTP Host headers do. Each app gets its
own external IP and an A record at `<app>.<domain>`.

## Prerequisites

- A Google Cloud project with billing enabled
- `gcloud`, Terraform 1.5+, Go 1.25+ (for local tests), and Docker credentials
  that can push to Artifact Registry (`gcloud auth configure-docker REGION-docker.pkg.dev`)
- A DNS domain you can delegate to Cloud DNS (or an existing Cloud DNS zone)

## Deploy

```bash
cd sshapp/terraform
cp terraform.tfvars.example terraform.tfvars
# edit project_id, domain, and optional CIDR allowlists

terraform init
terraform apply
```

If `create_dns_zone` is true (default), point your registrar at the name servers
in `terraform output dns_name_servers`.

Connect:

```bash
terraform output -json apps
ssh hello.YOUR_DOMAIN
```

The hello app prints `hello, <ssh-user>` and closes the session.

## Local app development

```bash
cd sshapp
go test ./...
go run ./apps/hello
# in another terminal:
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null localhost
```

## GitHub Actions (later)

After the cluster is healthy, set `github_repository = "OWNER/REPO"` and re-apply.
Use the outputs `github_actions_workload_identity_provider` and
`github_actions_service_account` with `google-github-actions/auth`. A workflow
that runs `terraform apply` (or a thinner deploy path) can follow; it is not
wired in this change.

## Destroy

```bash
cd sshapp/terraform
# if deletion_protection is true (default), set it false and apply first
terraform apply -var=deletion_protection=false
terraform destroy
```
