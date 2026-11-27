package substrate_test

import (
	"context"
	"os"
	"slices"
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
	// Inputs come from the node, so the actor reaches only cas, which gets
	// the tenant token, and the collector, which gets no credential.
	rules := map[string]*ateapi.HttpRule{}
	for _, rule := range policy.GetRules() {
		hosts := rule.GetHttp().GetHostnames()
		if len(hosts) != 1 {
			t.Fatalf("rule %v names %d hosts, want 1", rule, len(hosts))
		}
		rules[hosts[0]] = rule.GetHttp()
	}
	if len(rules) != 2 {
		t.Fatalf("rules %v, want cas and the collector", policy.GetRules())
	}
	headers := rules["cas.ci-substrate.svc.cluster.local"].GetEffects().GetReplaceHeaders()
	if len(headers) != 1 || headers[0].GetHeader() != "x-ci-substrate-tenant" {
		t.Errorf("cas rule %v does not inject the tenant header", rules["cas.ci-substrate.svc.cluster.local"])
	}
	if jwt := headers[0].GetActorJwt(); jwt == nil || !slices.Contains(jwt.GetAudiences(), "cas.ci-substrate.svc.cluster.local") {
		t.Errorf("cas rule %v does not inject an Actor JWT for cas", headers[0])
	}
	collector, ok := rules["otel-collector.ci-substrate.svc.cluster.local"]
	if !ok {
		t.Fatalf("no rule for the collector in %v", policy.GetRules())
	}
	if collector.GetEffects() != nil {
		t.Errorf("collector rule %v has effects; it must not carry a credential", collector)
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

type actorControl struct {
	ateapi.UnimplementedControlServer
	actors []*ateapi.Actor
}

func (c *actorControl) GetActorTemplate(context.Context, *ateapi.GetActorTemplateRequest) (*ateapi.ActorTemplate, error) {
	return &ateapi.ActorTemplate{}, nil
}

func (c *actorControl) ListActors(context.Context, *ateapi.ListActorsRequest) (*ateapi.ListActorsResponse, error) {
	return &ateapi.ListActorsResponse{Actors: c.actors}, nil
}

func TestListReportsWorkerPool(t *testing.T) {
	client := serve(t, &actorControl{actors: []*ateapi.Actor{{
		Metadata: &ateapi.ResourceMetadata{Name: "ci-runner-0"},
		Status: &ateapi.ActorStatus{
			State:            ateapi.ActorState_ACTOR_STATE_RUNNING,
			WorkerAssignment: &ateapi.WorkerAssignment{WorkerNamespace: "ci-substrate-workers", WorkerPool: "ci-runner"},
		},
	}, {
		Metadata: &ateapi.ResourceMetadata{Name: "ci-runner-1"},
		Status:   &ateapi.ActorStatus{State: ateapi.ActorState_ACTOR_STATE_SUSPENDED, AssignedNode: "node-a"},
	}}})
	manifest, err := os.ReadFile("../../deploy/substrate/egress-cas.yaml")
	if err != nil {
		t.Fatal(err)
	}
	actors, err := substrate.NewActors(t.Context(), client, "tenant-a", "ci-runner", manifest)
	if err != nil {
		t.Fatal(err)
	}
	got, err := actors.List(t.Context())
	if err != nil {
		t.Fatal(err)
	}
	// A suspended actor pinned to a node holds no worker.
	want := []actorpool.Actor{
		{Name: "ci-runner-0", State: actorpool.StateRunning, WorkerPool: "ci-substrate-workers/ci-runner"},
		{Name: "ci-runner-1", State: actorpool.StateSuspended},
	}
	if !slices.Equal(got, want) {
		t.Errorf("List() = %v, want %v", got, want)
	}
}
