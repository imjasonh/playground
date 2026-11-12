// Package substrate adapts Agent Substrate's control API to the actor pool.
// It owns the actors of one atespace that come from one ActorTemplate, and
// gives each new actor the tenant's egress policy before it first resumes, so
// the runner inside can reach only the cascache and cas Services and the
// gateway injects the tenant token on the way.
package substrate

import (
	"context"
	"crypto/tls"
	"crypto/x509"
	"errors"
	"fmt"
	"os"
	"strings"

	ateapi "go.ate.dev/substrate/api/ateapi/v1"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/encoding/protojson"
	"sigs.k8s.io/yaml"

	"github.com/imjasonh/playground/ci-substrate/internal/actorpool"
)

// Dial connects to ateapi at addr, verifying its serving certificate against
// the PEM bundle in caFile with serverName, and sending the bearer token read
// from tokenFile on every call. In the cluster both files are projected
// volumes: the servicedns ClusterTrustBundle and a ServiceAccount token whose
// audience is the API's Service name.
func Dial(addr, serverName, caFile, tokenFile string) (*grpc.ClientConn, error) {
	pem, err := os.ReadFile(caFile)
	if err != nil {
		return nil, err
	}
	pool := x509.NewCertPool()
	if !pool.AppendCertsFromPEM(pem) {
		return nil, fmt.Errorf("%s holds no certificates", caFile)
	}
	return grpc.NewClient(addr,
		grpc.WithTransportCredentials(credentials.NewTLS(&tls.Config{MinVersion: tls.VersionTLS13, RootCAs: pool, ServerName: serverName})),
		grpc.WithPerRPCCredentials(bearerFile(tokenFile)),
	)
}

// bearerFile reads the bearer token on every call, so a rotated projected
// token takes effect without a restart.
type bearerFile string

func (f bearerFile) GetRequestMetadata(context.Context, ...string) (map[string]string, error) {
	b, err := os.ReadFile(string(f))
	if err != nil {
		return nil, err
	}
	token := strings.TrimSpace(string(b))
	if token == "" {
		return nil, fmt.Errorf("%s is empty", string(f))
	}
	return map[string]string{"authorization": "Bearer " + token}, nil
}

func (bearerFile) RequireTransportSecurity() bool { return true }

// Actors implements actorpool.Actors for one atespace and template.
type Actors struct {
	client   ateapi.ControlClient
	atespace string
	template string
	policy   *ateapi.EgressPolicy
}

// NewActors returns an adapter that creates actors in atespace from template
// and gives each the egress policy in policyManifest, a YAML or JSON
// protojson EgressPolicy without metadata (the files under
// deploy/substrate/). It checks that the template exists.
func NewActors(ctx context.Context, client ateapi.ControlClient, atespace, template string, policyManifest []byte) (*Actors, error) {
	policy, err := ParseEgressPolicy(policyManifest)
	if err != nil {
		return nil, err
	}
	if _, err := client.GetActorTemplate(ctx, &ateapi.GetActorTemplateRequest{ActorTemplate: &ateapi.ObjectRef{Atespace: atespace, Name: template}}); err != nil {
		return nil, fmt.Errorf("actor template %s/%s: %w", atespace, template, err)
	}
	return &Actors{client: client, atespace: atespace, template: template, policy: policy}, nil
}

// ParseEgressPolicy reads an EgressPolicy manifest. The metadata is set at
// create time, so a manifest with one is rejected.
func ParseEgressPolicy(manifest []byte) (*ateapi.EgressPolicy, error) {
	j, err := yaml.YAMLToJSON(manifest)
	if err != nil {
		return nil, fmt.Errorf("egress policy manifest: %w", err)
	}
	policy := &ateapi.EgressPolicy{}
	if err := protojson.Unmarshal(j, policy); err != nil {
		return nil, fmt.Errorf("egress policy manifest: %w", err)
	}
	if policy.GetMetadata() != nil {
		return nil, errors.New("egress policy manifest: metadata is set per actor; leave it out")
	}
	if len(policy.GetRules()) == 0 {
		return nil, errors.New("egress policy manifest: no rules")
	}
	return policy, nil
}

func (a *Actors) ref(name string) *ateapi.ObjectRef {
	return &ateapi.ObjectRef{Atespace: a.atespace, Name: name}
}

// List returns every actor in the atespace with the pool's view of its
// state. The pool filters by name.
func (a *Actors) List(ctx context.Context) ([]actorpool.Actor, error) {
	var out []actorpool.Actor
	var token string
	for {
		resp, err := a.client.ListActors(ctx, &ateapi.ListActorsRequest{Atespace: a.atespace, Options: &ateapi.ListOptions{PageToken: token}})
		if err != nil {
			return nil, err
		}
		for _, actor := range resp.GetActors() {
			out = append(out, actorpool.Actor{Name: actor.GetMetadata().GetName(), State: State(actor.GetStatus().GetState())})
		}
		token = resp.GetNextPageToken()
		if token == "" {
			return out, nil
		}
	}
}

// State maps Substrate's actor state to the pool's.
func State(s ateapi.ActorState) actorpool.State {
	switch s {
	case ateapi.ActorState_ACTOR_STATE_SUSPENDED:
		return actorpool.StateSuspended
	case ateapi.ActorState_ACTOR_STATE_RESUMING:
		return actorpool.StateResuming
	case ateapi.ActorState_ACTOR_STATE_RUNNING:
		return actorpool.StateRunning
	case ateapi.ActorState_ACTOR_STATE_SUSPENDING:
		return actorpool.StateSuspending
	case ateapi.ActorState_ACTOR_STATE_CRASHED:
		return actorpool.StateCrashed
	default:
		return actorpool.StateUnknown
	}
}

// Create makes a suspended actor from the template and sets its egress
// policy. An actor that already exists from an earlier, interrupted Create
// just gets the policy.
func (a *Actors) Create(ctx context.Context, name string) error {
	actor := &ateapi.Actor{
		Metadata:      &ateapi.ResourceMetadata{Atespace: a.atespace, Name: name},
		ActorTemplate: a.ref(a.template),
	}
	if _, err := a.client.CreateActor(ctx, &ateapi.CreateActorRequest{Actor: actor}); err != nil && status.Code(err) != codes.AlreadyExists {
		return err
	}
	policy := &ateapi.EgressPolicy{
		Metadata: &ateapi.ResourceMetadata{Atespace: a.atespace, Name: "default"},
		Rules:    a.policy.GetRules(),
	}
	if _, err := a.client.CreateActorEgressPolicy(ctx, &ateapi.CreateActorEgressPolicyRequest{Actor: a.ref(name), EgressPolicy: policy}); err != nil && status.Code(err) != codes.AlreadyExists {
		return fmt.Errorf("egress policy: %w", err)
	}
	return nil
}

// Resume starts the actor from its snapshot, or from the image the first
// time.
func (a *Actors) Resume(ctx context.Context, name string) error {
	_, err := a.client.ResumeActor(ctx, &ateapi.ResumeActorRequest{Actor: a.ref(name)})
	return err
}

// Suspend checkpoints the actor and frees its worker.
func (a *Actors) Suspend(ctx context.Context, name string) error {
	_, err := a.client.SuspendActor(ctx, &ateapi.SuspendActorRequest{Actor: a.ref(name)})
	return err
}

// Delete removes the actor. A missing actor is not an error.
func (a *Actors) Delete(ctx context.Context, name string) error {
	_, err := a.client.DeleteActor(ctx, &ateapi.DeleteActorRequest{Actor: a.ref(name)})
	if status.Code(err) == codes.NotFound {
		return nil
	}
	return err
}
