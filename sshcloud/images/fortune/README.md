# fortune — sample SSH app

End-to-end sample for SSH App Cloud deploy. Implementation:
[`cmd/fortune`](../../cmd/fortune).

Fortune is **not** a gateway builtin. Deploy it like any other app with a
digest-pinned OCI image (Terraform builds one via `ko_build.fortune`).

```bash
# image digest after terraform apply:
terraform -chdir=sshcloud/terraform output -raw fortune_image

# then, as a joined user:
ssh deploy@GATEWAY
# App name: fortune
# Image: <fortune_image output>
# Tier: tiny
# Strategy: 1 (drain) or 2 (kick)

ssh fortune@GATEWAY
```

App contract: PID 1 listens on `:22`, trusts the platform user CA at `/ca.pub`
(injected by the agent) or `/run/platform/ssh_user_ca.pub`.

Local cert-hop testing without Firecracker (not the deploy path):

```bash
go build -o bin/fortune ./cmd/fortune
go run ./cmd/gateway -listen 127.0.0.1:2222 -fortune-bin ./bin/fortune
```
