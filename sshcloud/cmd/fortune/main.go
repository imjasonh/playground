// Command fortune is a sample SSH app: verifies platform user certs and prints a fortune.
package main

import (
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"os"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
)

var fortunes = []string{
	"The only way to do great work is to love what you do.",
	"ssh more, click less.",
	"MicroVMs are just very small computers with trust issues.",
	"Your future holds a short-lived SSH certificate.",
	"Fortune favors the joined.",
}

func main() {
	addr := flag.String("listen", "127.0.0.1:0", "listen address")
	caPath := flag.String("ca", "/run/platform/ssh_user_ca.pub", "platform user CA public key")
	hostKeyPath := flag.String("host-key", "", "host key path (ephemeral if empty)")
	flag.Parse()

	caBytes, err := os.ReadFile(*caPath)
	if err != nil {
		log.Fatalf("read CA: %v", err)
	}
	caPub, _, _, _, err := ssh.ParseAuthorizedKey(caBytes)
	if err != nil {
		log.Fatalf("parse CA: %v", err)
	}

	hostSigner, err := hostkey.LoadOrGenerate(*hostKeyPath)
	if err != nil {
		log.Fatalf("host key: %v", err)
	}

	checker := &ssh.CertChecker{
		IsUserAuthority: func(auth ssh.PublicKey) bool {
			return string(auth.Marshal()) == string(caPub.Marshal())
		},
	}
	cfg := &ssh.ServerConfig{
		PublicKeyCallback: checker.Authenticate,
	}
	cfg.AddHostKey(hostSigner)

	ln, err := net.Listen("tcp", *addr)
	if err != nil {
		log.Fatal(err)
	}
	// Supervisors parse the first line as the bound address.
	fmt.Println(ln.Addr().String())
	log.Printf("fortune listening on %s", ln.Addr())

	for {
		nc, err := ln.Accept()
		if err != nil {
			log.Fatal(err)
		}
		go handleConn(nc, cfg)
	}
}

func handleConn(nc net.Conn, cfg *ssh.ServerConfig) {
	defer nc.Close()
	sc, chans, reqs, err := ssh.NewServerConn(nc, cfg)
	if err != nil {
		return
	}
	defer sc.Close()
	go ssh.DiscardRequests(reqs)
	for newCh := range chans {
		if newCh.ChannelType() != "session" {
			_ = newCh.Reject(ssh.UnknownChannelType, "nope")
			continue
		}
		ch, creqs, err := newCh.Accept()
		if err != nil {
			continue
		}
		go handleSession(sc, ch, creqs)
	}
}

func handleSession(sc *ssh.ServerConn, ch ssh.Channel, reqs <-chan *ssh.Request) {
	defer ch.Close()
	for req := range reqs {
		switch req.Type {
		case "pty-req", "env", "window-change":
			if req.WantReply {
				_ = req.Reply(true, nil)
			}
		case "shell", "exec":
			if req.WantReply {
				_ = req.Reply(true, nil)
			}
			fmt.Fprintf(ch, "── fortune ──\r\n")
			fmt.Fprintf(ch, "hello %s\r\n", sc.User())
			fmt.Fprintf(ch, "%s\r\n", fortunes[rand.Intn(len(fortunes))])
			fmt.Fprintf(ch, "─────────────\r\n")
			_, _ = io.Copy(io.Discard, ch)
			_, _ = ch.SendRequest("exit-status", false, []byte{0, 0, 0, 0})
			return
		default:
			if req.WantReply {
				_ = req.Reply(false, nil)
			}
		}
	}
}
