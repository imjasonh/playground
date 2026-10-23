package gsgrpc

import (
	"context"
	"fmt"
	"net"
	"os"
	"time"

	"google.golang.org/api/option"
	"google.golang.org/grpc"
)

// storageLookupTimeout bounds the IPv4 lookup. gRPC's own resolver waits up
// to ResolvingTimeout (30s) before it publishes any address.
const storageLookupTimeout = 5 * time.Second

// storageDialTimeout bounds one TCP connect. gRPC would otherwise give the
// first address the whole minConnectTimeout (20s).
const storageDialTimeout = 5 * time.Second

// storageResolver looks up storage.googleapis.com. Tests replace it.
var storageResolver interface {
	LookupIP(ctx context.Context, network, host string) ([]net.IP, error)
} = &net.Resolver{PreferGo: true}

// dialOptions dials storage.googleapis.com over IPv4 when ipv4 is set.
//
// The gRPC DNS resolver does not publish addresses until its TXT lookup of
// _grpc_config.<host> returns, and that lookup ends only at its 30s timeout.
// The connect that follows can spend its 20s timeout on an unreachable IPv6
// address. A passthrough target also skips DirectPath. An emulator host
// keeps the default dial.
func dialOptions(ipv4 bool) []option.ClientOption {
	if !ipv4 || os.Getenv("STORAGE_EMULATOR_HOST_GRPC") != "" {
		return nil
	}
	return []option.ClientOption{
		option.WithEndpoint("passthrough:///storage.googleapis.com:443"),
		option.WithGRPCDialOption(grpc.WithDisableServiceConfig()),
		option.WithGRPCDialOption(grpc.WithContextDialer(dialStorage)),
	}
}

func dialStorage(ctx context.Context, addr string) (net.Conn, error) {
	host, port, err := net.SplitHostPort(addr)
	if err != nil {
		return nil, fmt.Errorf("storage dial address %q: %w", addr, err)
	}
	ips, err := resolveStorageIPv4(ctx, host)
	if err != nil {
		return nil, err
	}
	var dialer net.Dialer
	var last error
	for _, ip := range ips {
		dialCtx, cancel := context.WithTimeout(ctx, storageDialTimeout)
		conn, err := dialer.DialContext(dialCtx, "tcp4", net.JoinHostPort(ip.String(), port))
		cancel()
		if err == nil {
			return conn, nil
		}
		last = err
	}
	if last == nil {
		return nil, fmt.Errorf("no ipv4 address for %s", host)
	}
	return nil, last
}

func resolveStorageIPv4(ctx context.Context, host string) ([]net.IP, error) {
	if ip := net.ParseIP(host); ip != nil {
		if ip.To4() == nil {
			return nil, fmt.Errorf("storage dial address %s is not ipv4", host)
		}
		return []net.IP{ip}, nil
	}
	if host != "" && host[len(host)-1] != '.' {
		host += "."
	}
	lookupCtx, cancel := context.WithTimeout(ctx, storageLookupTimeout)
	defer cancel()
	ips, err := storageResolver.LookupIP(lookupCtx, "ip4", host)
	if err != nil {
		return nil, fmt.Errorf("lookup %s: %w", host, err)
	}
	var v4 []net.IP
	for _, ip := range ips {
		if ip.To4() != nil {
			v4 = append(v4, ip)
		}
	}
	if len(v4) == 0 {
		return nil, fmt.Errorf("no ipv4 address for %s", host)
	}
	return v4, nil
}
