package gsgrpc

import (
	"context"
	"net"
	"testing"
	"time"
)

type lookupFunc func(ctx context.Context, network, host string) ([]net.IP, error)

func (f lookupFunc) LookupIP(ctx context.Context, network, host string) ([]net.IP, error) {
	return f(ctx, network, host)
}

func TestDialOptionsIPv4(t *testing.T) {
	t.Setenv("STORAGE_EMULATOR_HOST_GRPC", "")
	if got := dialOptions(false); len(got) != 0 {
		t.Fatalf("dialOptions(false) = %d options, want none", len(got))
	}
	if got := dialOptions(true); len(got) != 3 {
		t.Fatalf("dialOptions(true) = %d options, want 3", len(got))
	}

	t.Setenv("STORAGE_EMULATOR_HOST_GRPC", "127.0.0.1:1")
	if got := dialOptions(true); len(got) != 0 {
		t.Fatalf("dialOptions(true) = %d options, want none when the emulator is set", len(got))
	}
}

func TestDialStorageUsesIPv4Name(t *testing.T) {
	ln, err := net.Listen("tcp4", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	_, port, err := net.SplitHostPort(ln.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	accepted := make(chan struct{})
	go func() {
		conn, err := ln.Accept()
		if err == nil {
			conn.Close()
			close(accepted)
		}
	}()

	prev := storageResolver
	storageResolver = lookupFunc(func(ctx context.Context, network, host string) ([]net.IP, error) {
		if network != "ip4" {
			t.Errorf("network = %q, want ip4", network)
		}
		if host != "storage.googleapis.com." {
			t.Errorf("host = %q, want absolute name", host)
		}
		return []net.IP{net.ParseIP("127.0.0.1"), net.ParseIP("2001:db8::1")}, nil
	})
	t.Cleanup(func() { storageResolver = prev })

	conn, err := dialStorage(context.Background(), "storage.googleapis.com:"+port)
	if err != nil {
		t.Fatal(err)
	}
	conn.Close()
	select {
	case <-accepted:
	case <-time.After(2 * time.Second):
		t.Fatal("listener did not accept")
	}
}

func TestDialStorageLiteralIPv4SkipsLookup(t *testing.T) {
	prev := storageResolver
	storageResolver = lookupFunc(func(context.Context, string, string) ([]net.IP, error) {
		t.Fatal("lookup called for a literal address")
		return nil, nil
	})
	t.Cleanup(func() { storageResolver = prev })

	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	// Nothing is listening. The dial must fail without a DNS lookup.
	if _, err := dialStorage(ctx, "127.0.0.1:1"); err == nil {
		t.Fatal("dialStorage error = nil")
	}
}

func TestResolveStorageIPv4RejectsIPv6Literal(t *testing.T) {
	if _, err := resolveStorageIPv4(context.Background(), "::1"); err == nil {
		t.Fatal("resolveStorageIPv4 error = nil")
	}
}
