# Chess

Multiplayer chess over SSH.

## Play

Through the shared sshapp mux:

```bash
ssh alice@ssh.YOUR_DOMAIN chess
# or bare ssh, then pick chess from the registry menu
```

Matchmaking is in-process. Keep Terraform at `replicas = 1` and
`deployment_strategy = "Recreate"` so both players share one pod and rolls
never briefly run two.

## Local

```bash
cd sshapp
go run ./apps/chess
# elsewhere:
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null localhost
```

Uses `SSHAPP_ADDR` (default `:2222`) and `SSHAPP_HOST_KEY_PATH` (default
`.ssh/host_ed25519`), same as the other Wish apps.

## Deploy

Wired in `sshapp/terraform` via `var.apps.chess`. Host keys and the ClusterIP
Service come from the shared `ssh_app` module; traffic enters through the mux
LoadBalancer.
