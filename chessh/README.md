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

## How SSH works on exe.dev

exe.dev's edge always dials an **injected sshd** inside the VM. A process
listening on port 22 in the container does not receive `ssh chessh.exe.xyz`.

CheSSH works with that model:

1. PID 1 runs `chessh serve` (wish on `127.0.0.1:2222`).
2. The login program for `root` / `ubuntu` is the **chessh binary itself**
   (not bash). Interactive SSH never drops you into a shell.
3. That login process sees `SSH_CONNECTION` and runs `play`, which opens a
   local SSH session to wish so you land in the game.

The image base is `ubuntu:24.04` only so the injected sshd has a normal user
database. You do not get an interactive Ubuntu shell.

## Running locally

```bash
go run ./ --local serve
```

Then in another terminal:

```bash
ssh localhost -p 2222
# or:
go run ./ --local play
```

`--local` writes an SSH host key under `~/.chessh/host_key` (or set
`SSH_HOST_KEY` / `SSH_HOST_KEY_FILE`).

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
