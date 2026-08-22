# Chess

Multiplayer chess over SSH.

## Play

```bash
ssh alice@ssh.YOUR_DOMAIN chess
```

Or connect with no command and pick chess from the mux menu.

Matchmaking is in-process. Terraform keeps `replicas = 1` and
`deployment_strategy = "Recreate"` so both players land on the same pod.

## Local

```bash
cd sshapp
go run ./apps/chess
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null localhost
```

Same env as the other Wish apps: `SSHAPP_ADDR` (default `:2222`) and
`SSHAPP_HOST_KEY_PATH` (default `.ssh/host_ed25519`).

## Deploy

`var.apps.chess` in `sshapp/terraform`. Traffic comes in through the mux
LoadBalancer; the app itself is ClusterIP-only.
