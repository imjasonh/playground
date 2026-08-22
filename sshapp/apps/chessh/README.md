# CheSSH

Multiplayer chess over SSH. Pronounced like "chess-ess-aych", or "chesh" in
your best Sean Connery impression.

## Play

Through the shared sshapp mux:

```bash
ssh alice@ssh.YOUR_DOMAIN chessh
# or bare ssh, then pick chessh from the registry menu
```

Matchmaking is in-process. Keep Terraform at `replicas = 1` so both players
land on the same pod.

## Local

```bash
cd sshapp
go run ./apps/chessh
# elsewhere:
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null localhost
```

Uses `SSHAPP_ADDR` (default `:2222`) and `SSHAPP_HOST_KEY_PATH` (default
`.ssh/host_ed25519`), same as the other Wish apps.

## Deploy

Wired in `sshapp/terraform` via `var.apps.chessh`. Host keys and the ClusterIP
Service come from the shared `ssh_app` module; traffic enters through the mux
LoadBalancer.
