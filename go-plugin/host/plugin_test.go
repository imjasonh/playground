package host

import (
	"bytes"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"plugin"
	"runtime"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/go-plugin/filter"
)

var (
	upperSO     string
	redactSO    string
	wrongtypeSO string
	nosymbolSO  string
	nilSO       string
)

func TestMain(m *testing.M) {
	if !pluginsSupported() {
		os.Exit(m.Run())
	}
	dir, err := os.MkdirTemp("", "go-plugin-")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	// os.Exit skips defers, so remove the plugin directory on each return.
	if err := buildPlugins(dir); err != nil {
		os.RemoveAll(dir)
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	code := m.Run()
	os.RemoveAll(dir)
	os.Exit(code)
}

func pluginsSupported() bool {
	switch runtime.GOOS {
	case "linux", "darwin", "freebsd":
	default:
		return false
	}
	return cgoEnabled
}

func moduleRoot() (string, error) {
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		return "", errors.New("runtime.Caller failed")
	}
	return filepath.Dir(filepath.Dir(file)), nil
}

func buildPlugins(dir string) error {
	root, err := moduleRoot()
	if err != nil {
		return err
	}
	pkgs := []struct {
		name string
		pkg  string
		dst  *string
	}{
		{"upper", "./plugins/upper", &upperSO},
		{"redact", "./plugins/redact", &redactSO},
		{"wrongtype", "./plugins/wrongtype", &wrongtypeSO},
		{"nosymbol", "./plugins/nosymbol", &nosymbolSO},
		{"nilfilter", "./plugins/nilfilter", &nilSO},
	}
	var wg sync.WaitGroup
	errc := make(chan error, len(pkgs))
	for _, p := range pkgs {
		wg.Add(1)
		go func(name, pkg string, dst *string) {
			defer wg.Done()
			out := filepath.Join(dir, name+".so")
			if err := buildPlugin(root, out, pkg); err != nil {
				errc <- err
				return
			}
			*dst = out
		}(p.name, p.pkg, p.dst)
	}
	wg.Wait()
	close(errc)
	var errs []error
	for err := range errc {
		errs = append(errs, err)
	}
	return errors.Join(errs...)
}

func buildPlugin(root, out, pkg string) error {
	args := []string{"build", "-buildmode=plugin", "-o", out, pkg}
	if raceEnabled {
		args = []string{"build", "-race", "-buildmode=plugin", "-o", out, pkg}
	}
	cmd := exec.Command("go", args...)
	cmd.Dir = root
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("go %s: %w\n%s", strings.Join(args, " "), err, output)
	}
	return nil
}

func requirePlugins(t *testing.T) {
	t.Helper()
	if upperSO == "" {
		t.Skip("Go plugins need cgo on linux, darwin, or freebsd")
	}
}

func TestSymbolShapes(t *testing.T) {
	requirePlugins(t)
	p, err := plugin.Open(upperSO)
	if err != nil {
		t.Fatal(err)
	}
	again, err := plugin.Open(upperSO)
	if err != nil {
		t.Fatal(err)
	}
	if p != again {
		t.Fatal("Open returned a second Plugin for the same path")
	}

	vsym, err := p.Lookup("V")
	if err != nil {
		t.Fatal(err)
	}
	n, ok := vsym.(*int)
	if !ok {
		t.Fatalf("V has type %T, want *int", vsym)
	}
	fsym, err := p.Lookup("F")
	if err != nil {
		t.Fatal(err)
	}
	fn, ok := fsym.(func() int)
	if !ok {
		t.Fatalf("F has type %T, want func() int", fsym)
	}
	if _, ok := fsym.(*func() int); ok {
		t.Fatal("F has type *func() int")
	}
	*n = 7
	if got := fn(); got != 7 {
		t.Fatalf("F() = %d after *V = 7", got)
	}

	psym, err := p.Lookup("Plugin")
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := psym.(filter.Filter); ok {
		t.Fatal("Plugin asserted directly to filter.Filter")
	}
	fp, ok := psym.(*filter.Filter)
	if !ok {
		t.Fatalf("Plugin has type %T, want *filter.Filter", psym)
	}
	got, err := (*fp).Apply("Go")
	if err != nil {
		t.Fatal(err)
	}
	if got != "GO" {
		t.Fatalf("Plugin.Apply = %q", got)
	}

	hsym, err := p.Lookup("Hook")
	if err != nil {
		t.Fatal(err)
	}
	hook, ok := hsym.(filter.Filter)
	if !ok {
		t.Fatalf("Hook has type %T, want filter.Filter", hsym)
	}
	if hook.Name() != "hook" {
		t.Fatalf("Hook.Name = %q", hook.Name())
	}

	isym, err := p.Lookup("Inited")
	if err != nil {
		t.Fatal(err)
	}
	inited, ok := isym.(*bool)
	if !ok {
		t.Fatalf("Inited has type %T, want *bool", isym)
	}
	if !*inited {
		t.Fatal("init had not set Inited")
	}

	count := 0
	for _, name := range filter.Registered() {
		if name == "upper" {
			count++
		}
	}
	if count != 1 {
		t.Fatalf("upper registered %d times", count)
	}
}

func TestLoadUpperAndRedact(t *testing.T) {
	requirePlugins(t)
	upper, err := Load(upperSO, nil)
	if err != nil {
		t.Fatal(err)
	}
	if upper.Name() != "upper" {
		t.Fatalf("Name = %q", upper.Name())
	}
	got, err := upper.Apply("Hello")
	if err != nil {
		t.Fatal(err)
	}
	if got != "HELLO" {
		t.Fatalf("Apply = %q", got)
	}

	if _, err := Load(redactSO, nil); err == nil {
		t.Fatal("redact accepted an empty config")
	}
	red, err := Load(redactSO, filter.Config{"word": "secret"})
	if err != nil {
		t.Fatal(err)
	}
	got, err = red.Apply("secret plan")
	if err != nil {
		t.Fatal(err)
	}
	if got != "*** plan" {
		t.Fatalf("redact Apply = %q", got)
	}

	other, err := Load(redactSO, filter.Config{"word": "plan"})
	if err != nil {
		t.Fatal(err)
	}
	got, err = other.Apply("secret plan")
	if err != nil {
		t.Fatal(err)
	}
	if got != "secret ***" {
		t.Fatalf("second redact Apply = %q", got)
	}

	got, err = Apply([]filter.Filter{red, upper}, "secret hello")
	if err != nil {
		t.Fatal(err)
	}
	if got != "*** HELLO" {
		t.Fatalf("chain = %q", got)
	}
}

func TestLoadRejectsBadPlugins(t *testing.T) {
	requirePlugins(t)
	if _, err := Load(wrongtypeSO, nil); err == nil {
		t.Fatal("wrong type was accepted")
	} else if !strings.Contains(err.Error(), "want") {
		t.Fatal(err)
	}
	if _, err := Load(nosymbolSO, nil); err == nil {
		t.Fatal("missing symbol was accepted")
	} else if !strings.Contains(err.Error(), "not found") {
		t.Fatal(err)
	}
	if _, err := Load(nilSO, nil); err == nil {
		t.Fatal("nil filter was accepted")
	} else if !strings.Contains(err.Error(), "nil") {
		t.Fatal(err)
	}

	missing := filepath.Join(t.TempDir(), "missing.so")
	if _, err := Load(missing, nil); err == nil {
		t.Fatal("missing file was accepted")
	}
	bad := filepath.Join(t.TempDir(), "bad.so")
	if err := os.WriteFile(bad, []byte("not a plugin"), 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := Load(bad, nil); err == nil {
		t.Fatal("non-plugin file was accepted")
	}
}

func TestRunCLILoadsPlugins(t *testing.T) {
	requirePlugins(t)
	var buf bytes.Buffer
	args := []string{
		"-filter", redactSO + "?word=secret",
		"-filter", upperSO,
	}
	if err := RunCLI(args, strings.NewReader("the secret word\n"), &buf); err != nil {
		t.Fatal(err)
	}
	if buf.String() != "THE *** WORD\n" {
		t.Fatalf("output = %q", buf.String())
	}
}
