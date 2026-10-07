package kube

import (
	"context"
	"errors"
	"flag"
	"log/slog"
	"os"
	"path/filepath"
	"slices"
	"testing"
)

// TestFlagsThatTheProgramDefines checks that Main leaves out its flags that
// the program defines itself, instead of panicking, and reads the rest.
func TestFlagsThatTheProgramDefines(t *testing.T) {
	fs := flag.NewFlagSet("program", flag.ContinueOnError)
	kubeconfig := fs.String("kubeconfig", "", "the program's own kubeconfig")
	verbose := fs.Bool("v", false, "the program's own verbosity")
	var m Manager
	level, skipped := m.flags(fs)
	if !slices.Equal(skipped, []string{"kubeconfig"}) {
		t.Errorf("skipped %q, want [kubeconfig]", skipped)
	}
	if err := fs.Parse([]string{"-kubeconfig=mine", "-v", "-watch-namespace=team", "-metrics-addr=:8080", "-shards=3", "-log-level=debug"}); err != nil {
		t.Fatal(err)
	}
	if *kubeconfig != "mine" || !*verbose || m.Kubeconfig != "" {
		t.Errorf("the program's -kubeconfig = %q and -v = %v, and the manager's Kubeconfig = %q; want mine, true, and empty", *kubeconfig, *verbose, m.Kubeconfig)
	}
	if m.Namespace != "team" || m.Addr != ":8080" || m.Shards != 3 || *level != slog.LevelDebug {
		t.Errorf("Namespace = %q, Addr = %q, Shards = %d, and -log-level = %v; want team, :8080, 3, and DEBUG", m.Namespace, m.Addr, m.Shards, *level)
	}
}

// TestFlagsDefaultToFields checks that Manager.Main keeps the fields that
// the program sets, as the defaults of their flags, and that a Manager with
// a Logger has no -log-level.
func TestFlagsDefaultToFields(t *testing.T) {
	fs := flag.NewFlagSet("program", flag.ContinueOnError)
	m := Manager{Namespace: "team", LeaderElection: true, Shards: 3, Addr: ":9090", Logger: slog.New(slog.DiscardHandler)}
	if level, _ := m.flags(fs); level != nil || fs.Lookup("log-level") != nil {
		t.Error("a Manager with a Logger has -log-level")
	}
	if err := fs.Parse([]string{"-metrics-addr=:7070"}); err != nil {
		t.Fatal(err)
	}
	if m.Namespace != "team" || !m.LeaderElection || m.Shards != 3 || m.Addr != ":7070" {
		t.Errorf("Namespace = %q, LeaderElection = %v, Shards = %d, and Addr = %q; want team, true, 3, and :7070", m.Namespace, m.LeaderElection, m.Shards, m.Addr)
	}
}

// TestRunSetup checks that Run runs Setup before it connects to the
// cluster, and returns Setup's error without connecting.
func TestRunSetup(t *testing.T) {
	missing := filepath.Join(t.TempDir(), "kubeconfig")
	want := errors.New("-zone is required")
	m := &Manager{Kubeconfig: missing, Setup: func(context.Context) error { return want }}
	if err := m.Run(t.Context()); err != want {
		t.Errorf("Run with a failing Setup = %v, want Setup's error", err)
	}
	ran := false
	m = &Manager{Kubeconfig: missing, Setup: func(context.Context) error {
		ran = true
		return nil
	}}
	if err := m.Run(t.Context()); !ran || !errors.Is(err, os.ErrNotExist) {
		t.Errorf("Run with a missing kubeconfig ran Setup = %v and returned %v; want true and an error about the kubeconfig", ran, err)
	}
}
