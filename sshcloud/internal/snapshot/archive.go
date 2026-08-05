package snapshot

import (
	"archive/tar"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
)

type archiveEntry struct {
	name  string
	limit int64
}

var archiveEntries = []archiveEntry{
	{name: "meta.json", limit: MaxMetadataBytes},
	{name: "vm.state", limit: MaxStateBytes},
	{name: "vm.mem", limit: MaxMemoryBytes},
	{name: "rootfs.ext4", limit: MaxRootfsBytes},
}

// WriteArchive writes the one accepted uncompressed package layout. File names,
// ordering, types, sizes, and metadata identity are all fixed before bytes are
// accepted by a remote publisher.
func WriteArchive(ctx context.Context, out io.Writer, ref Ref, pkg Package, expectedLayout string) error {
	if out == nil {
		return fmt.Errorf("snapshot archive writer is required")
	}
	meta, err := pkg.ReadMeta()
	if err != nil {
		return fmt.Errorf("read snapshot metadata: %w", err)
	}
	if err := ValidateMeta(ref, meta, expectedLayout); err != nil {
		return err
	}
	tw := tar.NewWriter(&contextWriter{ctx: ctx, out: out})
	for _, entry := range archiveEntries {
		source := filepath.Join(pkg.Dir, entry.name)
		info, err := os.Lstat(source)
		if err != nil {
			_ = tw.Close()
			return fmt.Errorf("stat snapshot entry %s: %w", entry.name, err)
		}
		if !info.Mode().IsRegular() || info.Size() <= 0 || info.Size() > entry.limit {
			_ = tw.Close()
			return fmt.Errorf("snapshot entry %s has invalid type or size %d", entry.name, info.Size())
		}
		header := &tar.Header{
			Name: entry.name, Mode: 0o600, Size: info.Size(),
			Typeflag: tar.TypeReg, Format: tar.FormatPAX,
		}
		if err := tw.WriteHeader(header); err != nil {
			_ = tw.Close()
			return err
		}
		file, err := os.Open(source)
		if err != nil {
			_ = tw.Close()
			return err
		}
		written, copyErr := io.Copy(tw, &contextReader{ctx: ctx, in: io.LimitReader(file, entry.limit+1)})
		closeErr := file.Close()
		if copyErr != nil {
			_ = tw.Close()
			return copyErr
		}
		if closeErr != nil {
			_ = tw.Close()
			return closeErr
		}
		if written != info.Size() {
			_ = tw.Close()
			return fmt.Errorf("snapshot entry %s changed while archiving", entry.name)
		}
	}
	if err := tw.Close(); err != nil {
		return err
	}
	return ctx.Err()
}

// ReadArchive validates and materializes exactly the fixed package layout.
func ReadArchive(ctx context.Context, in io.Reader, ref Ref, destDir, expectedLayout string) (Package, error) {
	pkg := NewPackageDir(destDir)
	if err := ref.Validate(); err != nil {
		return pkg, err
	}
	if in == nil {
		return pkg, fmt.Errorf("snapshot archive reader is required")
	}
	if _, err := os.Lstat(destDir); err == nil {
		return pkg, fmt.Errorf("snapshot destination already exists")
	} else if !os.IsNotExist(err) {
		return pkg, err
	}
	parent := filepath.Dir(destDir)
	if err := os.MkdirAll(parent, 0o700); err != nil {
		return pkg, err
	}
	tmp, err := os.MkdirTemp(parent, "."+filepath.Base(destDir)+".tmp-")
	if err != nil {
		return pkg, err
	}
	defer os.RemoveAll(tmp)

	tr := tar.NewReader(&contextReader{ctx: ctx, in: io.LimitReader(in, MaxRequestBytes+1)})
	var total int64
	for _, entry := range archiveEntries {
		header, err := tr.Next()
		if err != nil {
			return pkg, fmt.Errorf("read snapshot entry %s: %w", entry.name, err)
		}
		if header.Name != entry.name || header.Typeflag != tar.TypeReg ||
			header.Size <= 0 || header.Size > entry.limit {
			return pkg, fmt.Errorf("invalid snapshot archive entry %q", header.Name)
		}
		total += header.Size
		if total > MaxPackageBytes {
			return pkg, fmt.Errorf("snapshot package exceeds %d bytes", MaxPackageBytes)
		}
		target := filepath.Join(tmp, entry.name)
		file, err := os.OpenFile(target, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0o600)
		if err != nil {
			return pkg, err
		}
		written, copyErr := io.CopyN(file, tr, header.Size)
		closeErr := file.Close()
		if copyErr != nil {
			return pkg, fmt.Errorf("snapshot entry %s is truncated: %w", entry.name, copyErr)
		}
		if closeErr != nil {
			return pkg, closeErr
		}
		if written != header.Size {
			return pkg, fmt.Errorf("snapshot entry %s is truncated", entry.name)
		}
	}
	if header, err := tr.Next(); err != io.EOF {
		if err != nil {
			return pkg, fmt.Errorf("finish snapshot archive: %w", err)
		}
		return pkg, fmt.Errorf("unexpected snapshot archive entry %q", header.Name)
	}

	metaBytes, err := os.ReadFile(filepath.Join(tmp, "meta.json"))
	if err != nil {
		return pkg, err
	}
	var meta Meta
	decoder := json.NewDecoder(&limitedReader{reader: metaBytes, limit: MaxMetadataBytes})
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&meta); err != nil {
		return pkg, fmt.Errorf("decode snapshot metadata: %w", err)
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		return pkg, fmt.Errorf("snapshot metadata must contain one JSON object")
	}
	if err := ValidateMeta(ref, meta, expectedLayout); err != nil {
		return pkg, err
	}
	if err := os.Rename(tmp, destDir); err != nil {
		return pkg, err
	}
	pkg = NewPackageDir(destDir)
	pkg.Meta = meta
	return pkg, nil
}

type contextReader struct {
	ctx context.Context
	in  io.Reader
}

func (r *contextReader) Read(p []byte) (int, error) {
	if err := r.ctx.Err(); err != nil {
		return 0, err
	}
	return r.in.Read(p)
}

type contextWriter struct {
	ctx context.Context
	out io.Writer
}

func (w *contextWriter) Write(p []byte) (int, error) {
	if err := w.ctx.Err(); err != nil {
		return 0, err
	}
	return w.out.Write(p)
}

type limitedReader struct {
	reader []byte
	limit  int64
}

func (r *limitedReader) Read(p []byte) (int, error) {
	if r.limit <= 0 {
		return 0, io.EOF
	}
	if int64(len(r.reader)) > r.limit {
		r.reader = r.reader[:r.limit]
	}
	if len(r.reader) == 0 {
		return 0, io.EOF
	}
	n := copy(p, r.reader)
	r.reader = r.reader[n:]
	r.limit -= int64(n)
	return n, nil
}
