package a

import "testing"

func TestBad(t *testing.T) {
	go func() {
		t.Fatal("no") // want "call to Fatal from a non-test goroutine"
	}()
}

func TestFatalf(t *testing.T) {
	go func() {
		t.Fatalf("no") // want "call to Fatalf from a non-test goroutine"
	}()
}

func TestOk(t *testing.T) {
	t.Fatal("in test goroutine")
	go func() {
		t.Error("ok")
	}()
}
