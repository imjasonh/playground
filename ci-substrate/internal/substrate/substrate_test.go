package substrate_test

import (
	"os"
	"testing"

	ateapi "go.ate.dev/substrate/api/ateapi/v1"

	"github.com/imjasonh/playground/ci-substrate/internal/actorpool"
	"github.com/imjasonh/playground/ci-substrate/internal/substrate"
)

func TestParsesDeployedEgressPolicy(t *testing.T) {
	manifest, err := os.ReadFile("../../deploy/substrate/egress-cas.yaml")
	if err != nil {
		t.Fatal(err)
	}
	policy, err := substrate.ParseEgressPolicy(manifest)
	if err != nil {
		t.Fatal(err)
	}
	// Inputs come from the node, so cas is the actor's only egress.
	if len(policy.GetRules()) != 1 {
		t.Fatalf("rules %v, want cas only", policy.GetRules())
	}
	for _, rule := range policy.GetRules() {
		if hosts := rule.GetHttp().GetHostnames(); len(hosts) != 1 || hosts[0] != "cas.ci-substrate.svc.cluster.local" {
			t.Errorf("rule %v is not for cas", rule)
		}
		headers := rule.GetHttp().GetEffects().GetReplaceHeaders()
		if len(headers) != 1 || headers[0].GetHeader() != "x-ci-substrate-tenant" {
			t.Errorf("rule %v does not inject the tenant header", rule)
		}
	}
}

func TestRejectsBadManifests(t *testing.T) {
	for name, manifest := range map[string]string{
		"metadata":  "metadata: {atespace: a, name: default}\nrules:\n- http: {hostnames: ['*'], ports: {all: {}}}\n",
		"no rules":  "rules: []\n",
		"not yaml":  ": :\n",
		"bad field": "rules:\n- http: {hostname: x}\n",
	} {
		if _, err := substrate.ParseEgressPolicy([]byte(manifest)); err == nil {
			t.Errorf("%s: parsed", name)
		}
	}
}

func TestStateMapping(t *testing.T) {
	for in, want := range map[ateapi.ActorState]actorpool.State{
		ateapi.ActorState_ACTOR_STATE_SUSPENDED:   actorpool.StateSuspended,
		ateapi.ActorState_ACTOR_STATE_RESUMING:    actorpool.StateResuming,
		ateapi.ActorState_ACTOR_STATE_RUNNING:     actorpool.StateRunning,
		ateapi.ActorState_ACTOR_STATE_SUSPENDING:  actorpool.StateSuspending,
		ateapi.ActorState_ACTOR_STATE_CRASHED:     actorpool.StateCrashed,
		ateapi.ActorState_ACTOR_STATE_DELETING:    actorpool.StateUnknown,
		ateapi.ActorState_ACTOR_STATE_REVERTING:   actorpool.StateUnknown,
		ateapi.ActorState_ACTOR_STATE_UNSPECIFIED: actorpool.StateUnknown,
	} {
		if got := substrate.State(in); got != want {
			t.Errorf("State(%v) = %v, want %v", in, got, want)
		}
	}
}
