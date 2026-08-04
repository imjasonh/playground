# fortune — sample SSH app

Platform demo image for SSH App Cloud. Speaks SSH on `:22`, verifies
gateway-minted user certs using the CA at `/run/platform/ssh_user_ca.pub`, and
prints a fortune (or tiny PTY) on session open.

**Status:** placeholder. Implementation next (Go SSH server binary + Dockerfile /
ko-style build). Digest will be pinned when `deploy` / lazy-create wires it in.
