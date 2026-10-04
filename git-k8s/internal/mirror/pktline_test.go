package mirror

import (
	"bytes"
	"fmt"
	"io"
	"slices"
	"strconv"
	"strings"
	"testing"
)

func pkt(s string) string { return fmt.Sprintf("%04x%s", len(s)+4, s) }

var (
	zeroOID = strings.Repeat("0", 40)
	oidA    = strings.Repeat("a", 40)
	oidB    = strings.Repeat("b", 40)
	oid256  = strings.Repeat("c", 64)
)

func TestReadPush(t *testing.T) {
	update := func(old, new, ref string) string { return pkt(old + " " + new + " " + ref + "\n") }
	many := strings.Repeat(update(oidA, oidB, "refs/heads/x"), maxCommands+1) + "0000"
	shallow := func(n int) string { return strings.Repeat(pkt("shallow "+oidA+"\n"), n) }
	// An update of longRef takes 64000 bytes, so the mirror reads 16 of them.
	longRef := "refs/heads/" + strings.Repeat("x", 64000-4-83-11)
	long := func(n int) string { return strings.Repeat(update(oidA, oidB, longRef), n) + "0000" }
	for _, tc := range []struct {
		name     string
		in       string
		commands []command
		caps     []string
		err      string
	}{
		{name: "no updates", in: "0000"},
		{
			name:     "one update",
			in:       pkt(oidA+" "+oidB+" refs/heads/main\x00report-status side-band-64k agent=git/2\n") + "0000PACK",
			commands: []command{{Old: oidA, New: oidB, Ref: "refs/heads/main"}},
			caps:     []string{"report-status", "side-band-64k", "agent=git/2"},
		},
		{
			name: "a creation, an update, and a deletion",
			in:   pkt(zeroOID+" "+oidA+" refs/heads/new\x00report-status-v2\n") + update(oidA, oidB, "refs/heads/feature") + update(oidA, zeroOID, "refs/heads/old") + "0000",
			commands: []command{
				{Old: zeroOID, New: oidA, Ref: "refs/heads/new"},
				{Old: oidA, New: oidB, Ref: "refs/heads/feature"},
				{Old: oidA, New: zeroOID, Ref: "refs/heads/old"},
			},
			caps: []string{"report-status-v2"},
		},
		{
			name:     "shallow lines",
			in:       pkt("shallow "+oidA+"\n") + update(oidA, oidB, "refs/heads/main") + pkt("shallow "+oidB+"\n") + "0000",
			commands: []command{{Old: oidA, New: oidB, Ref: "refs/heads/main"}},
		},
		{
			// receive-pack reads a ref name up to a NUL on every line, so
			// the mirror must too.
			name: "capabilities on a later line",
			in:   update(oidA, oidB, "refs/heads/feature") + pkt(oidA+" "+oidB+" refs/heads/main\x00report-status\n") + "0000",
			commands: []command{
				{Old: oidA, New: oidB, Ref: "refs/heads/feature"},
				{Old: oidA, New: oidB, Ref: "refs/heads/main"},
			},
			caps: []string{"report-status"},
		},
		{
			name:     "no newline",
			in:       pkt(oidA+" "+oidB+" refs/heads/main") + "0000",
			commands: []command{{Old: oidA, New: oidB, Ref: "refs/heads/main"}},
		},
		{
			name:     "SHA-256",
			in:       update(oid256, oid256, "refs/heads/main") + "0000",
			commands: []command{{Old: oid256, New: oid256, Ref: "refs/heads/main"}},
		},
		{name: "a signed push", in: pkt("push-cert\x00report-status\n") + pkt("certificate version 0.1\n"), err: "signed pushes"},
		{name: "too many updates", in: many, err: "at most 1000 ref updates"},
		{
			name:     "as many lines as the mirror reads",
			in:       shallow(maxCommands-1) + update(oidA, oidB, "refs/heads/main") + "0000",
			commands: []command{{Old: oidA, New: oidB, Ref: "refs/heads/main"}},
		},
		{name: "too many shallow commits", in: shallow(maxCommands) + update(oidA, oidB, "refs/heads/main") + "0000", err: "at most 1000 ref updates and shallow commits"},
		{name: "as many bytes as the mirror reads", in: long(16), commands: slices.Repeat([]command{{Old: oidA, New: oidB, Ref: longRef}}, 16)},
		{name: "too many bytes", in: long(17), err: "at most 1048576 bytes of ref updates"},
		{name: "not an update", in: pkt("hello\n") + "0000", err: "malformed ref update"},
		{name: "an uppercase object name", in: update(strings.ToUpper(oidA), oidB, "refs/heads/main") + "0000", err: "malformed ref update"},
		{name: "a short object name", in: update("abc", oidB, "refs/heads/main") + "0000", err: "malformed ref update"},
		{name: "a space in the ref", in: update(oidA, oidB, "refs/heads/a b") + "0000", err: "malformed ref update"},
		{name: "no ref", in: update(oidA, oidB, "") + "0000", err: "malformed ref update"},
		{name: "no flush", in: update(oidA, oidB, "refs/heads/main"), err: "reading the ref updates: EOF"},
		{name: "a short packet", in: update(oidA, oidB, "refs/heads/main")[:20], err: "unexpected EOF"},
		{name: "a malformed length", in: "zzzz", err: "malformed packet length"},
		{name: "a delimiter packet", in: "0001", err: "unexpected packet length 1"},
		{name: "a packet that's too long", in: "fff1" + strings.Repeat("x", 0xfff1), err: "unexpected packet length"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			p, err := readPush(strings.NewReader(tc.in))
			if tc.err != "" {
				switch {
				case err == nil:
					t.Fatalf("readPush read %d updates; want an error with %q", len(p.commands), tc.err)
				case !strings.Contains(err.Error(), tc.err):
					t.Fatalf("readPush = %v; want an error with %q", err, tc.err)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if !slices.Equal(p.commands, tc.commands) || !slices.Equal(p.caps, tc.caps) {
				t.Errorf("readPush = %+v, %+v; want %+v, %+v", p.commands, p.caps, tc.commands, tc.caps)
			}
		})
	}
}

// demux reads a receive-pack response that uses a side band of up to size
// bytes per packet, and returns what it sent on band 1.
func demux(t *testing.T, resp []byte, size int) string {
	t.Helper()
	r := bytes.NewReader(resp)
	var band1 strings.Builder
	for {
		var hex [4]byte
		if _, err := io.ReadFull(r, hex[:]); err != nil {
			t.Fatalf("reading a packet length: %v", err)
		}
		n, err := strconv.ParseUint(string(hex[:]), 16, 16)
		if err != nil {
			t.Fatal(err)
		}
		if n == 0 {
			if r.Len() > 0 {
				t.Errorf("%d bytes after the final flush", r.Len())
			}
			return band1.String()
		}
		if int(n) > size {
			t.Errorf("a %d-byte packet in a side band of %d", n, size)
		}
		data := make([]byte, n-4)
		if _, err := io.ReadFull(r, data); err != nil {
			t.Fatal(err)
		}
		if data[0] != 1 {
			t.Errorf("a packet on band %d", data[0])
		}
		band1.Write(data[1:])
	}
}

func TestRefusal(t *testing.T) {
	long := strings.Repeat("x", 1500)
	reasons := []string{"main is a parent branch, which only the merge controller updates", long}
	commands := []command{{Old: oidA, New: oidB, Ref: "refs/heads/main"}, {Old: oidA, New: oidB, Ref: "refs/heads/feature"}}
	status := pkt("unpack ok\n") + pkt("ng refs/heads/main "+reasons[0]+"\n") + pkt("ng refs/heads/feature "+long+"\n") + "0000"

	got := refusal(&pushRequest{commands: commands, caps: []string{"report-status"}}, reasons)
	if string(got) != status {
		t.Errorf("without a side band, refusal = %q; want %q", got, status)
	}
	for capability, size := range map[string]int{"side-band-64k": maxPacket, "side-band": 1000} {
		got := refusal(&pushRequest{commands: commands, caps: []string{"report-status", capability}}, reasons)
		if band1 := demux(t, got, size); band1 != status {
			t.Errorf("with %s, band 1 holds %q; want %q", capability, band1, status)
		}
	}
}
