package gateway_test

import (
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestParseDeployArgs(t *testing.T) {
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	img := "ghcr.io/example/fortune@sha256:" + digest
	a, err := gateway.ParseDeployArgs([]string{
		"fortune", "--image=" + img, "--tier=tiny", "--strategy=kick", "--yes",
	})
	if err != nil {
		t.Fatal(err)
	}
	if a.Name != "fortune" || a.Image != img || a.Tier != "tiny" || a.Strategy != store.StrategyKick || !a.Yes {
		t.Fatalf("%+v", a)
	}

	a, err = gateway.ParseDeployArgs([]string{"fortune", "--image=" + img})
	if err != nil {
		t.Fatal(err)
	}
	if a.Tier != "tiny" || a.Strategy != store.StrategyDrain || a.Yes {
		t.Fatalf("defaults %+v", a)
	}

	_, err = gateway.ParseDeployArgs([]string{"fortune"})
	if err == nil || !strings.Contains(err.Error(), "--image") {
		t.Fatalf("got %v", err)
	}
	_, err = gateway.ParseDeployArgs([]string{"fortune", "--image=alpine:latest"})
	if err == nil || !strings.Contains(err.Error(), "digest") {
		t.Fatalf("got %v", err)
	}
}
