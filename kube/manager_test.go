package kube

import (
	"flag"
	"log/slog"
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
