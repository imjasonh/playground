# Substrate actor overlay

These files are applied **after** Agent Substrate
([agent-substrate/substrate](https://github.com/agent-substrate/substrate)) is
installed into the cluster with the `k8s.io` credential provider, and after
the `cas`/`cascache` control plane from `../` is already running. They are not
part of the default kind e2e: that e2e proves multi-tenancy and node-local
caching without Substrate, and it is what CI gates on.

For each CI tenant (the files show `tenant-a`):

1. Create the atespace `tenant-a`.
2. Apply `tenant-a-token.yaml` to put the tenant's token in its own
   namespace, and grant the `tenant-a` atespace that namespace in the
   `k8s-credential-provider-namespace-policy` ConfigMap.
3. Resolve and create the actor template:

   ```bash
   ko resolve -f runner-template.yaml > /tmp/runner-template.yaml
   kubectl ate create actor-template -f /tmp/runner-template.yaml
   ```

4. Create an actor per job from the template, create its egress policy from
   `egress-cascache.yaml` before it resumes, then resume it.

The runner in the actor sends a placeholder tenant header. The egress gateway
replaces it with the tenant's token, so the sandbox holds no credential.

Actor egress leaves the sandbox through the `atenet-egress` gateway, so the
gateway pod, not the actor, opens the connection to `cascache`. With
`internalTrafficPolicy: Local`, that connection reaches the cascache on the
gateway's node, not the actor's. The top-level README describes this gap and
how to close it.
