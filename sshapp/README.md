# sshapp — SSH apps on GKE Autopilot

`sshapp` runs Wish (SSH) apps on a GKE Autopilot cluster and publishes each one
at `<app>.<domain>` on port 22. There is no HTTP ingress. Terraform builds
images with [`ko_build`](https://registry.terraform.io/providers/ko-build/ko),
deploys them, and writes Cloud DNS A records to each Service LoadBalancer IP.

By default each app sits behind a small **activator** (Knative-style for SSH):
the LoadBalancer targets the activator, which scales the Wish Deployment from
0 to N on demand, holds the client TCP connection until a backend is ready,
then splices bytes. After idle, it scales back to 0.

## Layout

```
sshapp/
├── apps/
│   ├── hello/          # example Wish app
│   └── activator/      # TCP hold + scale-to-zero front
├── internal/
│   ├── proxy/          # accept → wait → splice
│   ├── scaler/         # Deployment 0↔N via the Kubernetes API
│   └── session/        # Snapshot Store (Memory + GCS) for app state dumps
├── terraform/
│   ├── modules/ssh_app/
│   └── *.tf
├── go.mod
└── README.md
```

To add another app:

1. Create `apps/<name>/` with a `main` package (Wish server on `:2222`).
2. Add an entry to `var.apps` in Terraform (see `terraform.tfvars.example`).
3. Apply. Terraform builds with `ko_build`, deploys, and creates `<name>.<domain>`.

## Scale to zero (activator)

SSH has no Host header. DNS for `<app>.domain` still points at a per-app
LoadBalancer IP. That IP hits the always-on activator, not the Wish pod.

```
client --TCP:22--> LB --> activator (always 1)
                           |  EnsureReady: scale Deployment 0→1
                           |  wait for Endpoints
                           |  dial pod:2222, splice
                           '  idle → scale to 0
```

Cold start feels like a slow SSH banner, not a refused connection. The activator
accepts TCP immediately and stays silent until the backend dial works; Wish then
sends `SSH-2.0-…` as usual.

Warm replicas default to **1**. Set `replicas` higher if you want parallel
sessions on separate pods once warm (the activator does not multiplex many
backends yet; it dials the first ready endpoint).

### Upgrades without hard drops

While a pod is serving sessions:

- RollingUpdate uses `maxUnavailable=0` / `maxSurge=1`, so a new pod comes up
  before the old one is killed.
- `terminationGracePeriodSeconds=45` gives Wish time to finish on SIGTERM.
- Existing TCP sessions stay on the old pod until they disconnect; new accepts
  go to ready pods.

The activator does **not** yet migrate a live SSH session onto a new pod. True
zero-downtime recycle for long-lived sessions needs app-level resume (below).

### Stateful apps and GCS

You cannot handle SIGKILL. Kubernetes sends SIGTERM first; after the grace
period it SIGKILLs. Dump state on SIGTERM (and on a periodic timer).

`internal/session` defines:

- `Store` — `Put`/`Get`/`Delete` for opaque blobs (`MemoryStore`, `GCSStore`)
- `Snapshotter` — app implements `Snapshot` / `Restore`

Intended loop:

1. Wish app serves a session with an id.
2. On SIGTERM (and every N seconds), `Snapshot()` → `Store.Put` to GCS.
3. On startup, if a snapshot exists for the session id (or a sticky cookie you
   invent), `Restore()` before accepting work.
4. Durable files go straight to GCS (or gcsfuse), not the container disk.

Sticky resume across activator re-splices is a later step: the activator would
pass a session id and the new pod would restore before SSH auth completes.

## Security model

- **Autopilot + private nodes.** Nodes have no public IPs. Egress uses Cloud NAT.
  Private Google Access covers Artifact Registry pulls.
- **SSH only.** Each app is a TCP LoadBalancer on port 22. No Ingress or HTTP.
- **Source ranges.** Set `ssh_allowed_cidrs` so the LoadBalancers are not open
  to the whole Internet unless you intend that.
- **Stable host keys.** Terraform generates an ED25519 host key per app and
  mounts it into the Wish pod.
- **Locked-down pods.** Non-root, read-only root filesystem, capabilities
  dropped. Activator mounts a service-account token (RBAC-scoped to one app).
- **Public-key auth only** on hello (accepts any key for the demo).
- **Workload Identity Federation for GitHub Actions** behind `github_repository`.

## Prerequisites

- A Google Cloud project with billing enabled
- `gcloud`, Terraform 1.5+, Go 1.26+ (for local tests), and Docker credentials
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

The first connect after idle may pause a few seconds while Autopilot schedules
the Wish pod. The hello app prints `hello, <ssh-user>` and closes.

## Local development

```bash
cd sshapp
go test ./...
go run ./apps/hello
# elsewhere:
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null localhost
```

The activator needs a cluster (or a fake `scaler.DeploymentScaler`) to exercise
end to end; unit tests cover hold-then-splice and idle scale-down without GKE.

## Cost sketch

With scale-to-zero, you pay for the activator pod continuously (~100m/256Mi) and
for Wish pods only while warm. The LoadBalancer and Cloud NAT still run full
time. Rough us-central1 idle cost drops versus leaving Wish at 1 replica 24/7,
but the LB (~$18/mo) and cluster fee (often free-tier) still dominate.

## GitHub Actions (later)

Set `github_repository = "OWNER/REPO"` and re-apply when you want WIF outputs
for `google-github-actions/auth`.

## Destroy

```bash
cd sshapp/terraform
terraform apply -var=deletion_protection=false
terraform destroy
```
