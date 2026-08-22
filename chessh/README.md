# CheSSH

A multiplayer chess game playable via SSH.

> [!IMPORTANT]
> It's pronounced like _"chess-ess-aych"_, or _"chesh"_ in your best Sean Connery impression.

## Play the game

```
ssh chessh.exe.xyz
```

You need an [exe.dev](https://exe.dev) account that can SSH to the VM
(owner or a shared user). `share set-public` on exe.dev is HTTPS-only; it
does not open SSH to the world.

![Screenshot of CheSSH gameplay](screenshot.png)

You may need to wait for another player, or open a second terminal to play
against yourself. Players are matched when they connect. When an opponent
disconnects, you win.

## How it runs on exe.dev

The container has no shell. CheSSH (wish) is PID 1 and listens on port 22.
exe.dev's SSH edge authenticates you, then dials that listener, so you land
in the game with no login shell hop.

The image is `gcr.io/distroless/static-debian12` (root, no shell) so the
process can bind port 22. Host keys are ephemeral in production; set
`SSH_HOST_KEY` or `SSH_HOST_KEY_FILE` if you need a stable one.

## Running locally

```bash
go run ./ --local
```

Then:

```bash
ssh localhost -p 2222
```

`--local` writes an SSH host key under `~/.chessh/host_key` and listens on
port 2222 (so it does not fight your machine's sshd).

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
