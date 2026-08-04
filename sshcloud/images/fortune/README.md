# fortune — sample SSH app

Platform demo for SSH App Cloud. Implementation lives at
[`cmd/fortune`](../../cmd/fortune): speaks SSH, verifies gateway-minted user
certs via `-ca` / `/run/platform/ssh_user_ca.pub`, prints a fortune.

```bash
# usually started by the gateway (-fortune-bin); manual:
go run ./cmd/fortune -listen 127.0.0.1:2223 -ca ./ssh_user_ca.pub
```

OCI/Firecracker packaging comes later; digest will be pinned when `deploy` /
lazy-create wires the microVM path.
