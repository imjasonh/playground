# Substrate actor overlay

These files are applied **after** Agent Substrate
([agent-substrate/substrate](https://github.com/agent-substrate/substrate)) is
installed into the cluster, and after the `cas`/`cascache` control plane from
`../` is already running. They are not part of the default kind e2e: that e2e
proves multi-tenancy and node-local caching without Substrate, which is the
headline of the demo and what CI gates on.

When Substrate is present:

1. Create one atespace per CI tenant.
2. Apply the actor templates with `kubectl ate create actor-template -f …`.
3. Create an actor per job from the matching template, resume it, and attach
   the egress policy that allows only the node-local cascache.

The templates assume:

* the node-local `cascache` DaemonSet is listening on host port `9092`
* the central `cas` Service is at `cas.ci-substrate.svc.cluster.local:8980`
* the runner binary is the `runner` image built by ko

See the top-level README for how this maps onto milestones M2–M5.
