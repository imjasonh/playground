package firecracker

import "testing"

func TestGuestBootArgs(t *testing.T) {
	t.Parallel()
	got := GuestBootArgs("172.16.1.2", "172.16.1.1", "255.255.255.0", "fortune")
	want := "ip=172.16.1.2::172.16.1.1:255.255.255.0:fortune:eth0:off"
	if got != want {
		t.Fatalf("got %q want %q", got, want)
	}
}

func TestAvailable(t *testing.T) {
	t.Parallel()
	// Just ensure it doesn't panic; value depends on host.
	_ = Available()
}
