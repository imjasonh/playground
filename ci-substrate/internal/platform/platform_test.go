package platform_test

import (
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/platform"
)

func TestRoundTripKeysAndActorNames(t *testing.T) {
	cases := []struct {
		spec platform.Spec
		key  string
	}{
		{platform.Spec{}, ""},
		{platform.Spec{Env: "warm-go"}, "env=warm-go"},
		{platform.Spec{Isolation: "clean"}, "isolation=clean"},
		{platform.Spec{Env: "warm-go", Isolation: "clean"}, "env=warm-go,isolation=clean"},
	}
	for _, tc := range cases {
		if got := tc.spec.Key(); got != tc.key {
			t.Errorf("%+v.Key() = %q, want %q", tc.spec, got, tc.key)
		}
		if got := platform.ParseKey(tc.key); got != tc.spec {
			t.Errorf("ParseKey(%q) = %+v, want %+v", tc.key, got, tc.spec)
		}
		name := platform.ActorName("ci-runner-", tc.spec, "a1b2c3d4e5f6")
		if len(name) > 63 {
			t.Errorf("ActorName(%+v) = %q exceeds 63 chars", tc.spec, name)
		}
		gotSpec, ok := platform.ParseActorName("ci-runner-", name)
		if !ok || gotSpec != tc.spec {
			t.Errorf("ParseActorName(%q) = (%+v, %v), want (%+v, true)", name, gotSpec, ok, tc.spec)
		}
	}
	if _, ok := platform.ParseActorName("ci-runner-", "other-actor"); ok {
		t.Fatal("ParseActorName matched non-prefixed actor")
	}
}

func TestFromActionFallsBackToCommand(t *testing.T) {
	cmd := &repb.Command{Platform: &repb.Platform{Properties: []*repb.Platform_Property{
		{Name: platform.PropEnv, Value: "go-127"},
	}}}
	if got := platform.FromAction(&repb.Action{}, cmd); got != (platform.Spec{Env: "go-127"}) {
		t.Fatalf("fallback = %+v, want env=go-127", got)
	}
	act := &repb.Action{Platform: &repb.Platform{Properties: []*repb.Platform_Property{
		{Name: platform.PropEnv, Value: "rust-185"},
		{Name: platform.PropIsolation, Value: "clean"},
	}}}
	if got := platform.FromAction(act, cmd); got != (platform.Spec{Env: "rust-185", Isolation: "clean"}) {
		t.Fatalf("action override = %+v", got)
	}
}

func TestSpecValidate(t *testing.T) {
	for _, valid := range []platform.Spec{
		{},
		{Env: "warm-go"},
		{Env: "a"},
		{Isolation: "clean"},
		{Env: "go-127", Isolation: "clean"},
	} {
		if err := valid.Validate(); err != nil {
			t.Errorf("Validate(%+v) = %v, want nil", valid, err)
		}
	}
	for _, invalid := range []platform.Spec{
		{Env: "UPPER"},
		{Env: "-leading"},
		{Env: "trailing-"},
		{Env: "has--double"},
		{Env: "a,isolation=clean"},
		{Env: "../escape"},
		{Env: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}, // 41 chars
		{Isolation: "bogus"},
	} {
		if err := invalid.Validate(); err == nil {
			t.Errorf("Validate(%+v) = nil, want error", invalid)
		}
	}
}
