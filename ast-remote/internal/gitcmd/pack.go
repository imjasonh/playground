package gitcmd

import (
	"bytes"
	"compress/zlib"
	"crypto/sha1"
	"encoding/binary"
	"fmt"
	"io"
)

// PackObject is one object to include in a packfile.
type PackObject struct {
	Kind string // blob/tree/commit/tag
	Data []byte // raw object content (no header)
}

func packType(kind string) (byte, error) {
	switch kind {
	case "commit":
		return 1, nil
	case "tree":
		return 2, nil
	case "blob":
		return 3, nil
	case "tag":
		return 4, nil
	default:
		return 0, fmt.Errorf("unsupported pack type %q", kind)
	}
}

// BuildPack constructs a git packfile (version 2) containing objs.
func BuildPack(objs []PackObject) ([]byte, error) {
	var body bytes.Buffer
	body.WriteString("PACK")
	_ = binary.Write(&body, binary.BigEndian, uint32(2))
	_ = binary.Write(&body, binary.BigEndian, uint32(len(objs)))

	for _, obj := range objs {
		typ, err := packType(obj.Kind)
		if err != nil {
			return nil, err
		}
		if err := writePackEntry(&body, typ, obj.Data); err != nil {
			return nil, err
		}
	}

	sum := sha1.Sum(body.Bytes())
	body.Write(sum[:])
	return body.Bytes(), nil
}

func writePackEntry(w *bytes.Buffer, typ byte, data []byte) error {
	size := len(data)
	b := byte((typ&7)<<4) | byte(size&0xf)
	size >>= 4
	for size != 0 {
		w.WriteByte(b | 0x80)
		b = byte(size & 0x7f)
		size >>= 7
	}
	w.WriteByte(b)

	zw, err := zlib.NewWriterLevel(w, zlib.BestSpeed)
	if err != nil {
		return err
	}
	if _, err := zw.Write(data); err != nil {
		return err
	}
	return zw.Close()
}

// IndexPack feeds a pack to `git index-pack --stdin`, installing it in the repo.
func (r *Repo) IndexPack(pack []byte) error {
	cmd := r.cmd("index-pack", "--stdin")
	cmd.Stdin = bytes.NewReader(pack)
	var stderr bytes.Buffer
	cmd.Stdout = io.Discard
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return fmt.Errorf("git index-pack: %w\n%s", err, stderr.String())
	}
	return nil
}
