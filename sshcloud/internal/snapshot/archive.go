package snapshot

import (
	"archive/tar"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
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

type validatedArchiveEntry struct {
	archiveEntry
	path string
	size int64
}

type validatedPackage struct {
	meta    Meta
	entries []validatedArchiveEntry
}

// ValidatePackage applies the same canonical directory, file, metadata, and
// size rules used by local copies and remote encrypted archives.
func ValidatePackage(ref Ref, pkg Package, expectedLayout string) (Meta, error) {
	validated, err := validatePackage(ref, pkg, expectedLayout)
	return validated.meta, err
}

func validatePackage(ref Ref, pkg Package, expectedLayout string) (validatedPackage, error) {
	if err := ref.Validate(); err != nil {
		return validatedPackage{}, err
	}
	canonical := NewPackageDir(pkg.Dir)
	if pkg.Dir == "" || pkg.StatePath != canonical.StatePath || pkg.MemPath != canonical.MemPath ||
		pkg.RootfsPath != canonical.RootfsPath || pkg.MetaPath != canonical.MetaPath {
		return validatedPackage{}, fmt.Errorf("snapshot package paths are not canonical")
	}
	dirInfo, err := os.Lstat(pkg.Dir)
	if err != nil {
		return validatedPackage{}, err
	}
	if !dirInfo.IsDir() || dirInfo.Mode()&os.ModeSymlink != 0 {
		return validatedPackage{}, fmt.Errorf("snapshot package directory is invalid")
	}
	dirEntries, err := os.ReadDir(pkg.Dir)
	if err != nil {
		return validatedPackage{}, err
	}
	gotNames := make([]string, 0, len(dirEntries))
	for _, entry := range dirEntries {
		gotNames = append(gotNames, entry.Name())
	}
	sort.Strings(gotNames)
	wantNames := make([]string, 0, len(archiveEntries))
	for _, entry := range archiveEntries {
		wantNames = append(wantNames, entry.name)
	}
	sort.Strings(wantNames)
	if len(gotNames) != len(wantNames) {
		return validatedPackage{}, fmt.Errorf("snapshot package must contain exactly %d entries", len(wantNames))
	}
	for i := range wantNames {
		if gotNames[i] != wantNames[i] {
			return validatedPackage{}, fmt.Errorf("unexpected snapshot package entry %q", gotNames[i])
		}
	}

	var validated validatedPackage
	var total int64
	for _, entry := range archiveEntries {
		source := filepath.Join(pkg.Dir, entry.name)
		info, err := os.Lstat(source)
		if err != nil {
			return validatedPackage{}, fmt.Errorf("stat snapshot entry %s: %w", entry.name, err)
		}
		if !info.Mode().IsRegular() || info.Size() <= 0 || info.Size() > entry.limit {
			return validatedPackage{}, fmt.Errorf("snapshot entry %s has invalid type or size %d", entry.name, info.Size())
		}
		total += info.Size()
		if total > MaxPackageBytes {
			return validatedPackage{}, fmt.Errorf("snapshot package exceeds %d bytes", MaxPackageBytes)
		}
		validated.entries = append(validated.entries, validatedArchiveEntry{
			archiveEntry: entry, path: source, size: info.Size(),
		})
	}
	meta, err := canonical.ReadMeta()
	if err != nil {
		return validatedPackage{}, fmt.Errorf("read snapshot metadata: %w", err)
	}
	if err := ValidateMeta(ref, meta, expectedLayout); err != nil {
		return validatedPackage{}, err
	}
	validated.meta = meta
	return validated, nil
}

// WriteArchive writes the one accepted uncompressed package layout. File names,
// ordering, types, sizes, and metadata identity are all fixed before bytes are
// accepted by a remote publisher.
func WriteArchive(ctx context.Context, out io.Writer, ref Ref, pkg Package, expectedLayout string) error {
	if out == nil {
		return fmt.Errorf("snapshot archive writer is required")
	}
	validated, err := validatePackage(ref, pkg, expectedLayout)
	if err != nil {
		return err
	}
	return writeValidatedArchive(ctx, out, validated)
}

func writeValidatedArchive(ctx context.Context, out io.Writer, pkg validatedPackage) error {
	tw := tar.NewWriter(&contextWriter{ctx: ctx, out: out})
	for _, entry := range pkg.entries {
		header := &tar.Header{
			Name: entry.name, Mode: 0o600, Size: entry.size,
			Typeflag: tar.TypeReg, Format: tar.FormatUSTAR,
		}
		if err := tw.WriteHeader(header); err != nil {
			_ = tw.Close()
			return err
		}
		file, err := os.Open(entry.path)
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
		if written != entry.size {
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
func ReadArchive(
	ctx context.Context,
	in io.Reader,
	ref Ref,
	destDir, expectedLayout string,
) (pkg Package, retErr error) {
	pkg = NewPackageDir(destDir)
	if err := ref.Validate(); err != nil {
		return pkg, err
	}
	if in == nil {
		return pkg, fmt.Errorf("snapshot archive reader is required")
	}
	if destDir == "" {
		return pkg, fmt.Errorf("snapshot destination is required")
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
	defer func() {
		if err := os.RemoveAll(tmp); err != nil {
			retErr = errors.Join(
				retErr,
				fmt.Errorf("clean snapshot archive staging: %w", err),
			)
		}
	}()

	limited := &io.LimitedReader{R: in, N: MaxRequestBytes + 1}
	source := &contextReader{ctx: ctx, in: limited}
	tr := tar.NewReader(source)
	var total int64
	for _, entry := range archiveEntries {
		header, err := tr.Next()
		if err != nil {
			return pkg, fmt.Errorf("read snapshot entry %s: %w", entry.name, err)
		}
		if header.Name != entry.name || header.Typeflag != tar.TypeReg ||
			header.Size <= 0 || header.Size > entry.limit || header.Mode != 0o600 ||
			header.Linkname != "" || header.Uid != 0 || header.Gid != 0 ||
			header.Uname != "" || header.Gname != "" ||
			header.Format != tar.FormatUSTAR || len(header.PAXRecords) != 0 {
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
	var trailing [1]byte
	if n, err := source.Read(trailing[:]); n != 0 || (err != nil && err != io.EOF) {
		return pkg, fmt.Errorf("snapshot archive contains trailing bytes")
	}

	validated, err := validatePackage(ref, NewPackageDir(tmp), expectedLayout)
	if err != nil {
		return pkg, err
	}
	if err := os.Rename(tmp, destDir); err != nil {
		return pkg, err
	}
	pkg = NewPackageDir(destDir)
	pkg.Meta = validated.meta
	return pkg, nil
}

// ClonePackage materializes a package through the canonical archive reader and
// writer so filesystem and remote stores accept exactly the same package set.
func ClonePackage(ctx context.Context, ref Ref, pkg Package, destDir, expectedLayout string) (Package, error) {
	reader, writer := io.Pipe()
	written := make(chan error, 1)
	go func() {
		writeErr := WriteArchive(ctx, writer, ref, pkg, expectedLayout)
		closeErr := writer.CloseWithError(writeErr)
		written <- errors.Join(writeErr, closeErr)
	}()
	cloned, readErr := ReadArchive(ctx, reader, ref, destDir, expectedLayout)
	if readErr != nil {
		_ = reader.CloseWithError(readErr)
	}
	writeErr := <-written
	if readErr != nil || writeErr != nil {
		return NewPackageDir(destDir), errors.Join(readErr, writeErr)
	}
	return cloned, nil
}

func decodeMeta(reader io.Reader) (Meta, error) {
	var meta Meta
	decoder := json.NewDecoder(io.LimitReader(reader, MaxMetadataBytes+1))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&meta); err != nil {
		return Meta{}, fmt.Errorf("decode snapshot metadata: %w", err)
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		return Meta{}, fmt.Errorf("snapshot metadata must contain one JSON object")
	}
	return meta, nil
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
