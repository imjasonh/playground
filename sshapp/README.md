# sshapp — SSH apps on GKE Autopilot

`sshapp` runs Wish (SSH) apps on a GKE Autopilot cluster behind **one** TCP
LoadBalancer. There is no HTTP ingress. Terraform builds images with
[`ko_build`](https://registry.terraform.io/providers/ko-build/ko), deploys each
app as a ClusterIP Service, and publishes DNS for `ssh.<domain>` plus `*.<domain>`
to that single LB IP.

A shared **mux** terminates SSH (so real usernames stay available). A bare
session gets an in-process app registry menu. Named apps (command path /
subsystem / `SSHAPP` env) scale from 0→N, then the mux SSH-proxies the session
to the Wish backend. After idle, it scales that app back to 0.

## Connect

Bare SSH hits the always-on mux registry (not a separate app pod):

```bash
ssh alice@ssh.YOUR_DOMAIN
# available apps:
#   1) hello
# select number or name (q to quit): 1
```

OpenSSH does not support `ssh host:foo/bar` (the part after `:` is a port, and
must be numeric). Skip the menu with a command path:

```bash
ssh alice@ssh.YOUR_DOMAIN hello
ssh alice@ssh.YOUR_DOMAIN foo/bar    # app=foo, args=["bar"]
```

Username is yours. The first path segment is the app.

For `ssh alice@hello.YOUR_DOMAIN` without typing the app name, add:

```sshconfig
Host *.YOUR_DOMAIN !ssh.YOUR_DOMAIN
  HostName ssh.YOUR_DOMAIN
  SetEnv SSHAPP=%n
```

`%n` is the original hostname (`hello.YOUR_DOMAIN`); the mux keeps the first
label. Clients need a recent OpenSSH that supports `SetEnv`.

## Layout

```
sshapp/
├── apps/
│   ├── chess/          # multiplayer chess (Wish + Bubble Tea)
│   ├── hello/          # example Wish app
│   ├── mux/            # shared SSH front + scale-to-zero
│   └── activator/      # optional raw-TCP activator (not used by Terraform)
├── internal/
│   ├── proxy/          # accept → wait → splice (TCP)
│   ├── registry/       # in-mux app menu (list + pick)
│   ├── route/          # command path / SSHAPP / subsystem → app
│   ├── scaler/         # Deployment 0↔N via the Kubernetes API
│   ├── session/        # Snapshot Store (Memory + GCS) for app state dumps
│   ├── sshpty/         # TERM/size defaults for pipe-backed OpenSSH PTYs
│   └── sshtea/         # Wish Bubble Tea middleware (mux-safe winCh)
├── e2e/                # KinD mux + hello (CI when sshapp/ changes)
├── terraform/
│   ├── modules/ssh_app/
│   └── *.tf
├── go.mod
└── README.md
```

To add another app:

1. Create `apps/<name>/` with a `main` package (Wish server on `:2222`).
   For Bubble Tea TUIs, use `sshtea.Middleware` (same shape as
   `wish/bubbletea.Middleware`) instead of Wish's stock one — see
   `internal/sshtea`.
2. Add an entry to `var.apps` in Terraform (see `terraform.tfvars.example`).
3. Apply. Terraform builds with `ko_build` and registers the name with the mux.

## Why one LoadBalancer

A GCP external passthrough forwarding rule is about $18/mo for the **first five**
rules together, then ~$7/mo per extra rule. Separate per-app LBs are therefore
not $18 each until you pass five apps—but one rule stays $18 no matter how many
apps you add, and you only pay for one external IP.

TCP has no Host header, so `<app>.domain` alone cannot select a backend on a
shared IP. The mux speaks SSH once, reads the app from the session (not the
username), then dials the right ClusterIP.

```
client --SSH:22--> LB --> mux (always 1)
                           |  no app? show registry menu in-process
                           |  else route: command / SSHAPP / subsystem
                           |  EnsureReady: scale Deployment 0→1
                           |  SSH-proxy to pod:2222
                           '  idle → scale that app to 0
```

Warm replicas default to **1**. Cold start feels like a slow SSH handshake while
Autopilot schedules the Wish pod.

### Upgrades without hard drops

While a pod is serving sessions:

- RollingUpdate uses `maxUnavailable=0` / `maxSurge=1`.
- `terminationGracePeriodSeconds=45` gives Wish time to finish on SIGTERM.
- Existing sessions stay on the old pod until they disconnect.

The mux does **not** migrate a live session onto a new pod. Long-lived resume
needs app-level snapshots (below).

### Stateful apps and GCS

You cannot handle SIGKILL. Dump state on SIGTERM (and on a periodic timer).

`internal/session` defines `Store` (`MemoryStore`, `GCSStore`) and `Snapshotter`
(`Snapshot` / `Restore`). Durable files should go to GCS (or gcsfuse), not the
container disk.

## Security model

- **Autopilot + private nodes.** No public node IPs. Egress via Cloud NAT.
- **One SSH LoadBalancer.** Source ranges via `ssh_allowed_cidrs`.
- **Stable mux host key.** Clients pin `ssh.<domain>` (and CNAMEd app names).
  Backend Wish host keys stay cluster-internal.
- **Locked-down pods.** Non-root, read-only root, capabilities dropped. Mux RBAC
  is limited to Deployments/Endpoints/Services in the apps namespace.
- **Public-key auth only** on mux and hello (accept any key for the demo).
- **Workload Identity Federation for GitHub Actions** behind `github_repository`.

## Prerequisites

- A Google Cloud project with billing enabled
- `gcloud`, Terraform 1.5+, Go 1.26+, and Docker credentials for Artifact Registry
- A DNS domain you can delegate to Cloud DNS (or an existing Cloud DNS zone)

## Deploy

```bash
cd sshapp/terraform
cp terraform.tfvars.example terraform.tfvars
# edit project_id, domain, and optional CIDR allowlists

# Remote state (required for CD; also fine for local). Create the bucket once.
#   gcloud storage buckets create gs://YOUR_TFSTATE_BUCKET --location=us-central1
terraform init \
  -backend-config=bucket=YOUR_TFSTATE_BUCKET \
  -backend-config=prefix=sshapp
terraform apply
```

If `create_dns_zone` is true (default), point your registrar at the name servers
in `terraform output dns_name_servers`.

Connect:

```bash
terraform output mux_fqdn
ssh "$(terraform output -raw mux_fqdn)"          # registry menu on the mux
ssh "$(terraform output -raw mux_fqdn)" hello    # skip the menu
```

## Local development

```bash
cd sshapp
go test ./...
go run ./apps/hello
# elsewhere:
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null localhost
```

## KinD e2e

PRs that touch `sshapp/` run a KinD e2e through `test.yml` (via
`test-go-modules.sh`): create a cluster, `ko build` mux + hello + chess into
it, apply `e2e/manifests/sshapp.yaml`, then check command-path routing for both
apps, the registry menu, and idle scale-to-zero.

```bash
cd sshapp
# Needs Docker, kubectl, and network to install kind/ko if missing.
SSHAPP_KIND_E2E=1 go test -v -timeout 20m ./e2e/
# Keep the cluster afterward:
SSHAPP_KIND_KEEP=1 SSHAPP_KIND_E2E=1 go test -v -timeout 20m ./e2e/
```

## Cost sketch

Idle, you pay for the mux (~100m–500m CPU / 256–512Mi), one LoadBalancer
(~$18/mo), Cloud NAT, and DNS. Wish pods scale to zero. Adding apps does not
add forwarding rules.

## GitHub Actions CD

`deploy-sshapp.yml` runs on pushes to `main` that touch `sshapp/` (and on
manual *Run workflow*). Until WIF is wired up it **exits 0** with a notice —
it will not fail the merge.

### Enable later

1. Bootstrap the stack locally (`terraform apply`) once, including:

   ```hcl
   github_repository = "imjasonh/playground"
   ```

2. Create a GCS bucket for Terraform state (if you have not already) and grant
   the deploy SA access on **that bucket only**, for example:

   ```bash
   gcloud storage buckets add-iam-policy-binding gs://YOUR_TFSTATE_BUCKET \
     --member="serviceAccount:$(terraform output -raw github_actions_service_account)" \
     --role=roles/storage.objectAdmin
   ```

3. Repo **variables**:

   | Variable | Value |
   |----------|-------|
   | `SSHAPP_WIF_PROVIDER` | `terraform output -raw github_actions_workload_identity_provider` |
   | `SSHAPP_DEPLOY_SA` | `terraform output -raw github_actions_service_account` |
   | `SSHAPP_TF_STATE_BUCKET` | the GCS bucket name |

4. Repo **secret** `SSHAPP_TFVARS`: contents of your `terraform.tfvars` (do not
   commit that file). Project ID lives there, not as a separate Actions var.

5. Re-run *Deploy sshapp* (or push a `sshapp/` change). The workflow authenticates
   with WIF and runs `terraform apply`, which rebuilds ko images and rolls the
   mux / app Deployments.

## Destroy

```bash
cd sshapp/terraform
terraform apply -var=deletion_protection=false
terraform destroy
```
