package taphelper

import (
	"context"
	"errors"
	"reflect"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
)

func TestIsolationRuleConstruction(t *testing.T) {
	t.Parallel()
	rules, err := IsolationRules("fc-0123abcdef89", "172.16.2.1")
	if err != nil {
		t.Fatal(err)
	}
	want := RuleSet{
		IPv4: []Rule{
			{
				Chain: "INPUT", InsertPosition: 1,
				Match: []string{
					"-i", "fc-0123abcdef89",
					"-s", "172.16.2.2/32",
					"-d", "172.16.2.1/32",
					"-m", "conntrack", "--ctstate", "ESTABLISHED,RELATED",
					"-j", "ACCEPT",
				},
			},
			{
				Chain: "INPUT", InsertPosition: 2,
				Match: []string{"-i", "fc-0123abcdef89", "-j", "DROP"},
			},
			{
				Chain: "FORWARD", InsertPosition: 1,
				Match: []string{"-i", "fc-0123abcdef89", "-j", "DROP"},
			},
		},
		IPv6: []Rule{
			{
				Chain: "INPUT", InsertPosition: 1,
				Match: []string{"-i", "fc-0123abcdef89", "-j", "DROP"},
			},
			{
				Chain: "FORWARD", InsertPosition: 1,
				Match: []string{"-i", "fc-0123abcdef89", "-j", "DROP"},
			},
		},
	}
	if !reflect.DeepEqual(rules, want) {
		t.Fatalf("rules = %#v, want %#v", rules, want)
	}
	for _, rule := range rules.IPv6 {
		if strings.Contains(strings.Join(rule.Match, " "), "ACCEPT") {
			t.Fatalf("IPv6 rule permits traffic: %#v", rule)
		}
	}
	if _, err := IsolationRules("../../tap0", "172.16.2.1"); err == nil {
		t.Fatal("arbitrary TAP name was accepted")
	}
}

func TestCreateRejectsArbitraryNetworkBeforeCommands(t *testing.T) {
	t.Parallel()
	runner := &recordingRunner{}
	server, err := NewServer(Config{
		SubnetBase: "172.16", ExpectedPeerUID: 991, Runner: runner,
		IPPath: "/fixed/ip", IPTablesPath: "/fixed/iptables", IP6TablesPath: "/fixed/ip6tables",
	})
	if err != nil {
		t.Fatal(err)
	}
	err = server.Create(context.Background(), CreateRequest{
		VMID: "0123abcdef89", HostIP: "10.0.0.1",
	})
	if err == nil {
		t.Fatal("out-of-range host IP was accepted")
	}
	if len(runner.calls) != 0 {
		t.Fatalf("validation executed commands: %v", runner.calls)
	}
}

func TestConfigRejectsNonFixedCommandPaths(t *testing.T) {
	t.Parallel()
	for _, path := range []string{"ip", "/fixed/../bin/ip", "/fixed/not-ip"} {
		_, err := NewServer(Config{
			SubnetBase: "172.16", ExpectedPeerUID: 991,
			IPPath: path, IPTablesPath: "/fixed/iptables", IP6TablesPath: "/fixed/ip6tables",
		})
		if err == nil {
			t.Errorf("IP command path %q was accepted", path)
		}
	}
}

type recordingRunner struct {
	calls  []string
	exists bool
	failAt string
}

func (r *recordingRunner) Run(_ context.Context, path string, args ...string) ([]byte, error) {
	call := path + " " + strings.Join(args, " ")
	r.calls = append(r.calls, call)
	if strings.Contains(call, " link show dev ") {
		if !r.exists {
			return nil, errors.New("missing")
		}
		return nil, nil
	}
	if strings.Contains(call, " tuntap add ") {
		r.exists = true
	}
	if strings.Contains(call, " link del dev ") {
		r.exists = false
	}
	if r.failAt != "" && strings.Contains(call, r.failAt) {
		return nil, errors.New("injected")
	}
	if strings.Contains(call, " -D ") || strings.Contains(call, " -C ") {
		return nil, errors.New("rule absent")
	}
	return nil, nil
}

func TestCreateFailureDeletesPartiallyPreparedTap(t *testing.T) {
	t.Parallel()
	runner := &recordingRunner{failAt: " addr add "}
	server, err := NewServer(Config{
		SubnetBase: "172.16", ExpectedPeerUID: 991, Runner: runner,
		IPPath: "/fixed/ip", IPTablesPath: "/fixed/iptables", IP6TablesPath: "/fixed/ip6tables",
	})
	if err != nil {
		t.Fatal(err)
	}
	err = server.Create(context.Background(), CreateRequest{
		VMID: "0123abcdef89", HostIP: "172.16.2.1",
	})
	if err == nil {
		t.Fatal("injected command failure was hidden")
	}
	if runner.exists {
		t.Fatal("partially configured TAP survived helper failure")
	}
	owner, _ := hostisolation.SandboxID("0123abcdef89")
	var sawOwnedAdd, sawDelete bool
	for _, call := range runner.calls {
		sawOwnedAdd = sawOwnedAdd || strings.Contains(call, "tuntap add dev fc-0123abcdef89 mode tap user "+uintString(owner))
		sawDelete = sawDelete || strings.Contains(call, "link del dev fc-0123abcdef89")
	}
	if !sawOwnedAdd || !sawDelete {
		t.Fatalf("calls did not use derived owner and rollback: %v", runner.calls)
	}
}

func uintString(value uint32) string {
	const digits = "0123456789"
	var buf [10]byte
	i := len(buf)
	for {
		i--
		buf[i] = digits[value%10]
		value /= 10
		if value == 0 {
			return string(buf[i:])
		}
	}
}
