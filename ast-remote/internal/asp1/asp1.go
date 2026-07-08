// Package asp1 implements the ASP1 tip stream: a zstd-compressed concatenation
// of raw git objects used for full-clone fast path.
//
// Wire format (v2, current):
//
//	"ASP1" | version(u8)=2 | codec(u8)=1 (zstd)
//	| nframes(u16be) | repeated: clen(u32be) | zstd(payload_i)
//
// Wire format (v1, still readable):
//
//	"ASP1" | version(u8)=1 | codec(u8)=1 (zstd) | zstd(payload)
//
// Payload (repeated):
//
//	type(u8) | oid(20) | size(u32be) | data[size]
//
// Types match git pack: 1=commit, 2=tree, 3=blob, 4=tag.
//
// Objects are encoded in path-sorted order (type, then path, then oid) so a
// large-window zstd pass can exploit cross-version similarity of same-path
// blobs. Multiple frames let fetch decompress and write in parallel.
package asp1

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"sync"
	"sync/atomic"

	"github.com/klauspost/compress/zlib"
	"github.com/klauspost/compress/zstd"
)

const (
	Magic      = "ASP1"
	Version    = 2
	VersionV1  = 1
	CodecZstd  = 1
	windowSize = 1 << 27 // 128 MiB
	numFrames  = 8
)

// Object is one git object to pack into an ASP1 stream.
type Object struct {
	Kind string // blob/tree/commit/tag
	OID  string // 40-hex
	Path string // optional path hint from rev-list --objects (for sort order)
	Data []byte // raw content (no git header)
}

func typeByte(kind string) (byte, error) {
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
		return 0, fmt.Errorf("asp1: unknown kind %q", kind)
	}
}

func kindFromType(tb byte) (string, error) {
	switch tb {
	case 1:
		return "commit", nil
	case 2:
		return "tree", nil
	case 3:
		return "blob", nil
	case 4:
		return "tag", nil
	default:
		return "", fmt.Errorf("asp1: bad type byte %d", tb)
	}
}

func typeOrd(kind string) int {
	switch kind {
	case "commit":
		return 0
	case "tree":
		return 1
	case "blob":
		return 2
	case "tag":
		return 3
	default:
		return 9
	}
}

// SortForEncode orders objects for zstd: type, then path, then oid.
// Same-path blob versions cluster so the compressor finds cross-revision deltas.
func SortForEncode(objs []Object) {
	sort.SliceStable(objs, func(i, j int) bool {
		ti, tj := typeOrd(objs[i].Kind), typeOrd(objs[j].Kind)
		if ti != tj {
			return ti < tj
		}
		if objs[i].Path != objs[j].Path {
			return objs[i].Path < objs[j].Path
		}
		return objs[i].OID < objs[j].OID
	})
}

func buildPayload(objs []Object) ([]byte, error) {
	var payload bytes.Buffer
	payload.Grow(estimatePayload(objs))
	for _, o := range objs {
		tb, err := typeByte(o.Kind)
		if err != nil {
			return nil, err
		}
		oid, err := hex.DecodeString(o.OID)
		if err != nil || len(oid) != 20 {
			return nil, fmt.Errorf("asp1: bad oid %q", o.OID)
		}
		if err := payload.WriteByte(tb); err != nil {
			return nil, err
		}
		if _, err := payload.Write(oid); err != nil {
			return nil, err
		}
		if err := binary.Write(&payload, binary.BigEndian, uint32(len(o.Data))); err != nil {
			return nil, err
		}
		if _, err := payload.Write(o.Data); err != nil {
			return nil, err
		}
	}
	return payload.Bytes(), nil
}

func compressPayload(payload []byte) ([]byte, error) {
	enc, err := zstd.NewWriter(nil,
		zstd.WithEncoderLevel(zstd.SpeedBetterCompression),
		zstd.WithWindowSize(windowSize),
	)
	if err != nil {
		return nil, err
	}
	comp := enc.EncodeAll(payload, make([]byte, 0, len(payload)/4))
	_ = enc.Close()
	return comp, nil
}

// Encode builds an ASP1 v2 multi-frame stream from objs.
// Objects are path-sorted; frames are encoded in parallel.
func Encode(objs []Object) ([]byte, error) {
	sorted := make([]Object, len(objs))
	copy(sorted, objs)
	SortForEncode(sorted)

	frames := splitFrames(sorted, numFrames)
	comps := make([][]byte, len(frames))
	errCh := make(chan error, 1)
	var wg sync.WaitGroup
	for i, chunk := range frames {
		wg.Add(1)
		go func(i int, chunk []Object) {
			defer wg.Done()
			payload, err := buildPayload(chunk)
			if err != nil {
				select {
				case errCh <- err:
				default:
				}
				return
			}
			comp, err := compressPayload(payload)
			if err != nil {
				select {
				case errCh <- err:
				default:
				}
				return
			}
			comps[i] = comp
		}(i, chunk)
	}
	wg.Wait()
	select {
	case err := <-errCh:
		return nil, err
	default:
	}

	var out bytes.Buffer
	out.WriteString(Magic)
	out.WriteByte(Version)
	out.WriteByte(CodecZstd)
	_ = binary.Write(&out, binary.BigEndian, uint16(len(comps)))
	for _, c := range comps {
		_ = binary.Write(&out, binary.BigEndian, uint32(len(c)))
		out.Write(c)
	}
	return out.Bytes(), nil
}

func splitFrames(objs []Object, n int) [][]Object {
	if len(objs) == 0 {
		return nil
	}
	if n < 1 {
		n = 1
	}
	if n > len(objs) {
		n = len(objs)
	}
	chunk := (len(objs) + n - 1) / n
	var frames [][]Object
	for i := 0; i < len(objs); i += chunk {
		end := i + chunk
		if end > len(objs) {
			end = len(objs)
		}
		frames = append(frames, objs[i:end])
	}
	return frames
}

func estimatePayload(objs []Object) int {
	n := 0
	for _, o := range objs {
		n += 25 + len(o.Data)
	}
	return n
}

func parsePayload(payload []byte) ([]Object, error) {
	var objs []Object
	off := 0
	for off < len(payload) {
		if off+25 > len(payload) {
			return nil, fmt.Errorf("asp1: truncated entry at %d", off)
		}
		kind, err := kindFromType(payload[off])
		if err != nil {
			return nil, err
		}
		oid := hex.EncodeToString(payload[off+1 : off+21])
		size := binary.BigEndian.Uint32(payload[off+21 : off+25])
		off += 25
		if off+int(size) > len(payload) {
			return nil, fmt.Errorf("asp1: truncated data for %s", oid)
		}
		data := payload[off : off+int(size)]
		off += int(size)
		objs = append(objs, Object{Kind: kind, OID: oid, Data: data})
	}
	return objs, nil
}

// Decode decompresses an ASP1 stream into objects (does not write to disk).
func Decode(stream []byte) ([]Object, error) {
	frames, err := framePayloads(stream)
	if err != nil {
		return nil, err
	}
	var objs []Object
	for _, p := range frames {
		part, err := parsePayload(p)
		if err != nil {
			return nil, err
		}
		objs = append(objs, part...)
	}
	return objs, nil
}

func framePayloads(stream []byte) ([][]byte, error) {
	if len(stream) < 6 || string(stream[:4]) != Magic {
		return nil, fmt.Errorf("asp1: bad magic")
	}
	ver := stream[4]
	if stream[5] != CodecZstd {
		return nil, fmt.Errorf("asp1: unsupported codec %d", stream[5])
	}
	switch ver {
	case VersionV1:
		dec, err := zstd.NewReader(nil, zstd.WithDecoderMaxWindow(1<<30))
		if err != nil {
			return nil, err
		}
		defer dec.Close()
		payload, err := dec.DecodeAll(stream[6:], nil)
		if err != nil {
			return nil, err
		}
		return [][]byte{payload}, nil
	case Version:
		if len(stream) < 8 {
			return nil, fmt.Errorf("asp1: truncated v2 header")
		}
		n := int(binary.BigEndian.Uint16(stream[6:8]))
		off := 8
		out := make([][]byte, n)
		var wg sync.WaitGroup
		errCh := make(chan error, 1)
		type job struct {
			i   int
			raw []byte
		}
		jobs := make([]job, 0, n)
		for i := 0; i < n; i++ {
			if off+4 > len(stream) {
				return nil, fmt.Errorf("asp1: truncated frame %d len", i)
			}
			clen := int(binary.BigEndian.Uint32(stream[off : off+4]))
			off += 4
			if off+clen > len(stream) {
				return nil, fmt.Errorf("asp1: truncated frame %d data", i)
			}
			jobs = append(jobs, job{i, stream[off : off+clen]})
			off += clen
		}
		for _, j := range jobs {
			wg.Add(1)
			go func(j job) {
				defer wg.Done()
				dec, err := zstd.NewReader(nil, zstd.WithDecoderMaxWindow(1<<30))
				if err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				payload, err := dec.DecodeAll(j.raw, nil)
				dec.Close()
				if err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				out[j.i] = payload
			}(j)
		}
		wg.Wait()
		select {
		case err := <-errCh:
			return nil, err
		default:
		}
		return out, nil
	default:
		return nil, fmt.Errorf("asp1: unsupported version %d", ver)
	}
}

// Install writes ASP1 objects as loose objects under gitDir/objects.
// Frames are decompressed and written in parallel. Store-produced streams are
// trusted (no per-object SHA-1 verify). zlib uses BestSpeed.
func Install(gitDir string, stream []byte) (int, error) {
	objDir := filepath.Join(gitDir, "objects")
	for i := 0; i < 256; i++ {
		if err := os.MkdirAll(filepath.Join(objDir, fmt.Sprintf("%02x", i)), 0o755); err != nil {
			return 0, err
		}
	}

	if len(stream) < 6 || string(stream[:4]) != Magic {
		return 0, fmt.Errorf("asp1: bad magic")
	}
	ver := stream[4]
	if stream[5] != CodecZstd {
		return 0, fmt.Errorf("asp1: unsupported codec %d", stream[5])
	}

	var total atomic.Int64
	errCh := make(chan error, 1)

	installPayload := func(payload []byte) {
		type entry struct {
			kind string
			oid  string
			data []byte
		}
		var entries []entry
		off := 0
		for off < len(payload) {
			if off+25 > len(payload) {
				select {
				case errCh <- fmt.Errorf("asp1: truncated entry at %d", off):
				default:
				}
				return
			}
			kind, err := kindFromType(payload[off])
			if err != nil {
				select {
				case errCh <- err:
				default:
				}
				return
			}
			oid := hex.EncodeToString(payload[off+1 : off+21])
			size := int(binary.BigEndian.Uint32(payload[off+21 : off+25]))
			off += 25
			if off+size > len(payload) {
				select {
				case errCh <- fmt.Errorf("asp1: truncated data for %s", oid):
				default:
				}
				return
			}
			entries = append(entries, entry{kind, oid, payload[off : off+size]})
			off += size
		}

		workers := runtime.GOMAXPROCS(0)
		if workers < 2 {
			workers = 2
		}
		if workers > 16 {
			workers = 16
		}
		jobs := make(chan entry, workers*8)
		var wg sync.WaitGroup
		worker := func() {
			defer wg.Done()
			var zbuf bytes.Buffer
			zw, _ := zlib.NewWriterLevel(&zbuf, zlib.BestSpeed)
			hdr := make([]byte, 0, 64)
			for e := range jobs {
				hdr = hdr[:0]
				hdr = append(hdr, e.kind...)
				hdr = append(hdr, ' ')
				hdr = append(hdr, fmt.Sprintf("%d", len(e.data))...)
				hdr = append(hdr, 0)
				zbuf.Reset()
				zw.Reset(&zbuf)
				if _, err := zw.Write(hdr); err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				if _, err := zw.Write(e.data); err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				if err := zw.Close(); err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				path := filepath.Join(objDir, e.oid[:2], e.oid[2:])
				if err := os.WriteFile(path, zbuf.Bytes(), 0o444); err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
			}
		}
		wg.Add(workers)
		for i := 0; i < workers; i++ {
			go worker()
		}
		for _, e := range entries {
			jobs <- e
		}
		close(jobs)
		wg.Wait()
		total.Add(int64(len(entries)))
	}

	switch ver {
	case VersionV1:
		dec, err := zstd.NewReader(nil, zstd.WithDecoderMaxWindow(1<<30))
		if err != nil {
			return 0, err
		}
		payload, err := dec.DecodeAll(stream[6:], nil)
		dec.Close()
		if err != nil {
			return 0, err
		}
		installPayload(payload)
	case Version:
		if len(stream) < 8 {
			return 0, fmt.Errorf("asp1: truncated v2 header")
		}
		n := int(binary.BigEndian.Uint16(stream[6:8]))
		off := 8
		type frame struct {
			raw []byte
		}
		frames := make([]frame, 0, n)
		for i := 0; i < n; i++ {
			if off+4 > len(stream) {
				return 0, fmt.Errorf("asp1: truncated frame %d len", i)
			}
			clen := int(binary.BigEndian.Uint32(stream[off : off+4]))
			off += 4
			if off+clen > len(stream) {
				return 0, fmt.Errorf("asp1: truncated frame %d data", i)
			}
			frames = append(frames, frame{stream[off : off+clen]})
			off += clen
		}
		var wg sync.WaitGroup
		for _, fr := range frames {
			wg.Add(1)
			go func(raw []byte) {
				defer wg.Done()
				dec, err := zstd.NewReader(nil, zstd.WithDecoderMaxWindow(1<<30))
				if err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				payload, err := dec.DecodeAll(raw, nil)
				dec.Close()
				if err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				installPayload(payload)
			}(fr.raw)
		}
		wg.Wait()
	default:
		return 0, fmt.Errorf("asp1: unsupported version %d", ver)
	}

	select {
	case err := <-errCh:
		return 0, err
	default:
	}
	return int(total.Load()), nil
}
