# CheSSH

A multiplayer chess game playable via SSH.

> [!IMPORTANT]
> It's pronounced like _"chess-ess-aych"_, or _"chesh"_ in your best Sean Connery impression.

## Play the game

```
ssh chessh.exe.xyz
```

You need an [exe.dev](https://exe.dev) account and SSH access to the `chessh`
VM (owner, or `share add <email> --root`). exe.dev brokers SSH; there is no
anonymous public SSH. The community Terraform `exedev_vm` resource also has no
`public` flag — `share set-public` only opens the HTTPS proxy, not SSH.

![Screenshot of CheSSH gameplay](screenshot.png)

You may need to wait for another player, or open a second terminal to play
against yourself. Players are matched when they connect. When an opponent
disconnects, you win.

## Running locally

```bash
go run ./ --local
```

Then:

```bash
ssh localhost -p 2222
```

`--local` writes an SSH host key under `~/.chessh/host_key` (or set
`SSH_HOST_KEY` / `SSH_HOST_KEY_FILE` yourself). On exe.dev the process
mints an ephemeral host key; clients talk to exe.dev's SSH broker, so
there is nothing to manage in Terraform.

## Deploying

Infrastructure lives in `iac/` and targets [exe.dev](https://exe.dev):

- `ko_build` builds the Go binary and pushes
  `ghcr.io/imjasonh/playground/chessh` to GHCR
- `exedev_vm` runs that image as the `chessh` VM (`chessh.exe.xyz`)
- Terraform state is stored in Cloudflare R2
  (`playground-terraform-state` / `exe/chessh/terraform.tfstate`)

On merges to `main` that touch `chessh/`, `.github/workflows/deploy-exe.yml`
applies the stack (same idea as `deploy-workers.yml` for Cloudflare Workers).
You can also apply by hand after minting an exe.dev API token and short-lived
R2 credentials:

```bash
cd iac/
# Set EXEDEV_TOKEN and docker-login to ghcr.io first.
export CLOUDFLARE_API_TOKEN=...
export CLOUDFLARE_ACCOUNT_ID=...
bash ../../.github/scripts/mint-r2-temp-credentials.sh
terraform init \
  -backend-config="endpoints={s3=\"https://$CLOUDFLARE_ACCOUNT_ID.r2.cloudflarestorage.com\"}"
terraform apply
```

### Repo secrets for CI

| Secret | Purpose |
|--------|---------|
| `EXEDEV_SSH_PRIVATE_KEY` | OpenSSH private key whose public half is registered on exe.dev; CI mints `EXEDEV_TOKEN` from it. Prefer an unencrypted key (GitHub encrypts secrets). |
| `EXEDEV_SSH_PASSPHRASE` | Optional. Passphrase if `EXEDEV_SSH_PRIVATE_KEY` is encrypted. |
| `CLOUDFLARE_ACCOUNT_ID` | Already used by Worker deploys; R2 S3 endpoint host |
| `CLOUDFLARE_API_TOKEN` | Creates the state bucket if missing, and is the parent for short-lived R2 S3 credentials (needs R2 Object Read & Write on `playground-terraform-state`) |

The GHCR package must be **public** so exe.dev can pull the image (the
community `exedev` provider has no `registry_auth`). Make it public once in
the GitHub Packages UI after the first push.
