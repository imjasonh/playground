package certs

import (
	"crypto/tls"
	"crypto/x509"
	"io"
	"testing"
	"time"
)

func TestServingCertificate(t *testing.T) {
	now := time.Now()
	ca, err := NewCA("test-ca", now)
	if err != nil {
		t.Fatal(err)
	}
	hosts := []string{"web.shop.svc", "web.shop.svc.cluster.local", "127.0.0.1"}
	serving, err := NewServing(ca, hosts, now)
	if err != nil {
		t.Fatal(err)
	}
	if !Usable(ca, serving, hosts, now) {
		t.Error("a new serving certificate isn't usable")
	}
	if Usable(ca, serving, []string{"other.shop.svc"}, now) {
		t.Error("the certificate is usable for a host it doesn't name")
	}
	if Usable(ca, serving, hosts, now.Add(ServingValidity-Renew+time.Hour)) {
		t.Error("the certificate is usable inside its renewal period")
	}
	other, err := NewCA("other-ca", now)
	if err != nil {
		t.Fatal(err)
	}
	if Usable(other, serving, hosts, now) {
		t.Error("the certificate is usable with a CA that didn't sign it")
	}
	if ExpiresSoon(ca, now) || !ExpiresSoon(ca, now.Add(CAValidity-time.Hour)) {
		t.Error("ExpiresSoon is wrong")
	}
	if !ValidAt(ca.Cert, now) || ValidAt(ca.Cert, now.Add(CAValidity+time.Hour)) || ValidAt([]byte("junk"), now) {
		t.Error("ValidAt is wrong")
	}
}

func TestHandshake(t *testing.T) {
	now := time.Now()
	ca, err := NewCA("test-ca", now)
	if err != nil {
		t.Fatal(err)
	}
	serving, err := NewServing(ca, []string{"127.0.0.1"}, now)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := tls.X509KeyPair(serving.Cert, serving.Key)
	if err != nil {
		t.Fatal(err)
	}
	ln, err := tls.Listen("tcp", "127.0.0.1:0", &tls.Config{Certificates: []tls.Certificate{cert}, MinVersion: tls.VersionTLS12})
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	go func() {
		c, err := ln.Accept()
		if err != nil {
			return
		}
		defer c.Close()
		_, _ = io.WriteString(c, "hello")
	}()
	pool := x509.NewCertPool()
	pool.AppendCertsFromPEM(ca.Cert)
	c, err := tls.Dial("tcp", ln.Addr().String(), &tls.Config{RootCAs: pool, ServerName: "127.0.0.1", MinVersion: tls.VersionTLS12})
	if err != nil {
		t.Fatalf("handshake verified against the CA failed: %v", err)
	}
	defer c.Close()
	b, _ := io.ReadAll(c)
	if string(b) != "hello" {
		t.Errorf("read %q", b)
	}
}
