package mirror

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"slices"
	"strconv"
	"strings"
)

const (
	// maxPacket is the longest pkt-line, with its length.
	maxPacket = 65520
	// maxCommands is the most ref updates that the mirror takes in one
	// push.
	maxCommands = 1000
)

// command is one ref update in a push. Old or New is all zeros when the
// update creates or deletes the ref.
type command struct {
	Old, New, Ref string
}

// pushRequest is the start of a receive-pack request: its ref updates, and
// the capabilities that the client asked for.
type pushRequest struct {
	commands []command
	caps     []string
}

func (p *pushRequest) has(capability string) bool { return slices.Contains(p.caps, capability) }

// readPush reads the ref updates at the start of a receive-pack request, up
// to the flush packet that ends them. It reads each line the way that
// receive-pack does, so that the updates it returns are the ones that
// receive-pack makes: without a trailing newline, the update ends at the
// first NUL, and capabilities follow the NUL on any line.
func readPush(r io.Reader) (*pushRequest, error) {
	p := &pushRequest{}
	for {
		line, flush, err := readPacket(r)
		switch {
		case err != nil:
			return nil, err
		case flush:
			return p, nil
		case strings.HasPrefix(line, "shallow "):
			continue
		case strings.HasPrefix(line, "push-cert"):
			return nil, errors.New("the mirror doesn't take signed pushes")
		case len(p.commands) == maxCommands:
			return nil, fmt.Errorf("the mirror takes at most %d ref updates in one push", maxCommands)
		}
		line, caps, _ := strings.Cut(strings.TrimSuffix(line, "\n"), "\x00")
		p.caps = append(p.caps, strings.Fields(caps)...)
		f := strings.Split(line, " ")
		if len(f) != 3 || !isOID(f[0]) || !isOID(f[1]) || f[2] == "" {
			return nil, fmt.Errorf("malformed ref update %.100q", line)
		}
		p.commands = append(p.commands, command{Old: f[0], New: f[1], Ref: f[2]})
	}
}

// readPacket reads one pkt-line, or reports a flush packet.
func readPacket(r io.Reader) (line string, flush bool, err error) {
	var size [4]byte
	if _, err := io.ReadFull(r, size[:]); err != nil {
		return "", false, fmt.Errorf("reading the ref updates: %w", err)
	}
	n, err := strconv.ParseUint(string(size[:]), 16, 32)
	switch {
	case err != nil:
		return "", false, fmt.Errorf("malformed packet length %q", size[:])
	case n == 0:
		return "", true, nil
	case n <= 4 || n > maxPacket:
		return "", false, fmt.Errorf("unexpected packet length %d", n)
	}
	buf := make([]byte, n-4)
	if _, err := io.ReadFull(r, buf); err != nil {
		return "", false, fmt.Errorf("reading the ref updates: %w", err)
	}
	return string(buf), false, nil
}

func isOID(s string) bool {
	if len(s) != 40 && len(s) != 64 {
		return false
	}
	for _, c := range []byte(s) {
		if !('0' <= c && c <= '9' || 'a' <= c && c <= 'f') {
			return false
		}
	}
	return true
}

func isZero(oid string) bool { return strings.Trim(oid, "0") == "" }

// refusal is a receive-pack response that refuses every update in p, each
// for its reason, which git shows to the person who pushed.
func refusal(p *pushRequest, reasons []string) []byte {
	var status bytes.Buffer
	writePacket(&status, "unpack ok\n")
	for i, c := range p.commands {
		writePacket(&status, "ng "+c.Ref+" "+reasons[i]+"\n")
	}
	status.WriteString("0000")
	size := 0
	switch {
	case p.has("side-band-64k"):
		size = maxPacket
	case p.has("side-band"):
		size = 1000
	default:
		return status.Bytes()
	}
	// With a side band, the status goes in band 1, split into packets.
	var out bytes.Buffer
	for data := status.Bytes(); len(data) > 0; {
		n := min(len(data), size-5)
		fmt.Fprintf(&out, "%04x\x01", n+5)
		out.Write(data[:n])
		data = data[n:]
	}
	out.WriteString("0000")
	return out.Bytes()
}

func writePacket(b *bytes.Buffer, s string) {
	fmt.Fprintf(b, "%04x%s", len(s)+4, s)
}
