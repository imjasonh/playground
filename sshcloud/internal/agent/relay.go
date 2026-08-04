package agent

import (
	"errors"
	"fmt"
	"io"
	"net"
	"sync"
	"syscall"
	"time"
)

// tcpRelay exposes an agent-host address for a guest-local SSH endpoint. Guest
// TAP addresses are intentionally not routed across the VPC.
type tcpRelay struct {
	listener net.Listener
	target   string

	mu     sync.Mutex
	closed bool
	conns  map[net.Conn]struct{}
}

func startTCPRelay(host, target string, firstPort, lastPort, offset int) (*tcpRelay, error) {
	if net.ParseIP(host) == nil {
		return nil, fmt.Errorf("relay host must be an IP address, got %q", host)
	}
	if firstPort < 1 || lastPort > 65535 || firstPort > lastPort {
		return nil, fmt.Errorf("invalid relay port range %d-%d", firstPort, lastPort)
	}
	count := lastPort - firstPort + 1
	for i := 0; i < count; i++ {
		port := firstPort + (offset+i)%count
		ln, err := net.Listen("tcp", net.JoinHostPort(host, fmt.Sprint(port)))
		if err != nil {
			if !errors.Is(err, syscall.EADDRINUSE) {
				return nil, fmt.Errorf("listen relay on %s:%d: %w", host, port, err)
			}
			continue
		}
		r := &tcpRelay{
			listener: ln,
			target:   target,
			conns:    make(map[net.Conn]struct{}),
		}
		go r.serve()
		return r, nil
	}
	return nil, fmt.Errorf("no relay port available on %s in %d-%d", host, firstPort, lastPort)
}

func (r *tcpRelay) Addr() string { return r.listener.Addr().String() }

func (r *tcpRelay) serve() {
	for {
		conn, err := r.listener.Accept()
		if err != nil {
			r.mu.Lock()
			closed := r.closed
			r.mu.Unlock()
			if closed {
				return
			}
			time.Sleep(25 * time.Millisecond)
			continue
		}
		r.mu.Lock()
		if r.closed {
			r.mu.Unlock()
			_ = conn.Close()
			return
		}
		r.conns[conn] = struct{}{}
		r.mu.Unlock()
		go r.proxy(conn)
	}
}

func (r *tcpRelay) proxy(client net.Conn) {
	defer func() {
		_ = client.Close()
		r.mu.Lock()
		delete(r.conns, client)
		r.mu.Unlock()
	}()
	guest, err := net.DialTimeout("tcp", r.target, 5*time.Second)
	if err != nil {
		return
	}
	defer guest.Close()

	done := make(chan struct{}, 2)
	copyHalf := func(dst, src net.Conn) {
		_, _ = io.Copy(dst, src)
		if tcp, ok := dst.(*net.TCPConn); ok {
			_ = tcp.CloseWrite()
		}
		done <- struct{}{}
	}
	go copyHalf(guest, client)
	go copyHalf(client, guest)
	<-done
	<-done
}

func (r *tcpRelay) Close() error {
	if r == nil {
		return nil
	}
	r.mu.Lock()
	if r.closed {
		r.mu.Unlock()
		return nil
	}
	r.closed = true
	err := r.listener.Close()
	for conn := range r.conns {
		_ = conn.Close()
	}
	r.mu.Unlock()
	return err
}
