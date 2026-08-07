package agent

import (
	"io"
	"net"
	"testing"
	"time"
)

func TestTCPRelay(t *testing.T) {
	t.Parallel()
	guest, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer guest.Close()
	go func() {
		conn, err := guest.Accept()
		if err != nil {
			return
		}
		defer conn.Close()
		_, _ = io.Copy(conn, conn)
	}()

	relay, err := startTCPRelay("127.0.0.1", guest.Addr().String(), 26000, 26999, 0)
	if err != nil {
		t.Fatal(err)
	}
	defer relay.Close()

	conn, err := net.DialTimeout("tcp", relay.Addr(), time.Second)
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	if _, err := conn.Write([]byte("hello")); err != nil {
		t.Fatal(err)
	}
	got := make([]byte, 5)
	if _, err := io.ReadFull(conn, got); err != nil {
		t.Fatal(err)
	}
	if string(got) != "hello" {
		t.Fatalf("got %q", got)
	}
}
