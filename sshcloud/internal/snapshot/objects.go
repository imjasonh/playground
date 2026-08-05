package snapshot

import (
	"context"
	"errors"
	"fmt"
	"io"
	"path"
	"strings"

	"cloud.google.com/go/storage"
	"google.golang.org/api/googleapi"
	"google.golang.org/api/iterator"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var (
	ErrObjectNotFound     = errors.New("snapshot object not found")
	ErrObjectPrecondition = errors.New("snapshot object generation precondition failed")
)

type ObjectAttrs struct {
	Generation int64
	Size       int64
}

type ObjectCondition struct {
	DoesNotExist    bool
	Generation      int64
	MatchGeneration bool
}

// ObjectStore is the generation-aware blob boundary used by EnvelopeStore.
// Tests inject an in-memory implementation; production uses GCSObjects.
type ObjectStore interface {
	Write(context.Context, string, ObjectCondition, func(io.Writer) error) (ObjectAttrs, error)
	Read(context.Context, string, int64) (io.ReadCloser, ObjectAttrs, error)
	Stat(context.Context, string) (ObjectAttrs, error)
	Delete(context.Context, string, int64) error
	Health(context.Context) error
	Close() error
}

type GCSObjects struct {
	bucket string
	client *storage.Client
}

func NewGCSObjects(ctx context.Context, bucket string) (*GCSObjects, error) {
	if strings.TrimSpace(bucket) == "" {
		return nil, fmt.Errorf("snapshot bucket is required")
	}
	client, err := storage.NewClient(ctx)
	if err != nil {
		return nil, err
	}
	return &GCSObjects{bucket: bucket, client: client}, nil
}

func (g *GCSObjects) object(name string, condition ObjectCondition) *storage.ObjectHandle {
	object := g.client.Bucket(g.bucket).Object(name)
	switch {
	case condition.DoesNotExist:
		object = object.If(storage.Conditions{DoesNotExist: true})
	case condition.MatchGeneration:
		object = object.If(storage.Conditions{GenerationMatch: condition.Generation})
	}
	return object
}

func (g *GCSObjects) Write(ctx context.Context, name string, condition ObjectCondition, write func(io.Writer) error) (ObjectAttrs, error) {
	if err := validateObjectName(name); err != nil {
		return ObjectAttrs{}, err
	}
	if write == nil {
		return ObjectAttrs{}, fmt.Errorf("object writer callback is required")
	}
	writeCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	writer := g.object(name, condition).NewWriter(writeCtx)
	writer.ChunkSize = 16 << 20
	if err := write(writer); err != nil {
		cancel()
		_ = writer.Close()
		return ObjectAttrs{}, err
	}
	if err := writer.Close(); err != nil {
		return ObjectAttrs{}, mapObjectError(err)
	}
	attrs := writer.Attrs()
	return ObjectAttrs{Generation: attrs.Generation, Size: attrs.Size}, nil
}

func (g *GCSObjects) Read(ctx context.Context, name string, generation int64) (io.ReadCloser, ObjectAttrs, error) {
	if err := validateObjectName(name); err != nil {
		return nil, ObjectAttrs{}, err
	}
	object := g.client.Bucket(g.bucket).Object(name)
	if generation > 0 {
		object = object.If(storage.Conditions{GenerationMatch: generation})
	}
	reader, err := object.NewReader(ctx)
	if err != nil {
		return nil, ObjectAttrs{}, mapObjectError(err)
	}
	return reader, ObjectAttrs{Generation: reader.Attrs.Generation, Size: reader.Attrs.Size}, nil
}

func (g *GCSObjects) Stat(ctx context.Context, name string) (ObjectAttrs, error) {
	if err := validateObjectName(name); err != nil {
		return ObjectAttrs{}, err
	}
	attrs, err := g.client.Bucket(g.bucket).Object(name).Attrs(ctx)
	if err != nil {
		return ObjectAttrs{}, mapObjectError(err)
	}
	return ObjectAttrs{Generation: attrs.Generation, Size: attrs.Size}, nil
}

func (g *GCSObjects) Delete(ctx context.Context, name string, generation int64) error {
	if err := validateObjectName(name); err != nil {
		return err
	}
	object := g.client.Bucket(g.bucket).Object(name)
	if generation > 0 {
		object = object.If(storage.Conditions{GenerationMatch: generation})
	}
	err := object.Delete(ctx)
	if errors.Is(err, storage.ErrObjectNotExist) {
		return nil
	}
	err = mapObjectError(err)
	if errors.Is(err, ErrObjectNotFound) {
		return nil
	}
	return err
}

func (g *GCSObjects) Health(ctx context.Context) error {
	// Object Admin deliberately does not grant storage.buckets.get. A
	// prefix-scoped list proves the exact object data-plane permission used by
	// this service without broadening snapshotd's bucket IAM.
	iter := g.client.Bucket(g.bucket).Objects(ctx, &storage.Query{Prefix: ".sshcloud-health/"})
	_, err := iter.Next()
	if err == iterator.Done {
		return nil
	}
	return mapObjectError(err)
}

func (g *GCSObjects) Close() error {
	if g == nil || g.client == nil {
		return nil
	}
	return g.client.Close()
}

func validateObjectName(name string) error {
	if name == "" || path.Clean(name) != name || strings.HasPrefix(name, "/") ||
		strings.Contains(name, `\`) || strings.ContainsRune(name, '\x00') {
		return fmt.Errorf("invalid internal snapshot object name")
	}
	return nil
}

func mapObjectError(err error) error {
	if err == nil {
		return nil
	}
	if errors.Is(err, storage.ErrObjectNotExist) || status.Code(err) == codes.NotFound {
		return fmt.Errorf("%w: %v", ErrObjectNotFound, err)
	}
	var apiErr *googleapi.Error
	if errors.As(err, &apiErr) && (apiErr.Code == 409 || apiErr.Code == 412) {
		return fmt.Errorf("%w: %v", ErrObjectPrecondition, err)
	}
	if status.Code(err) == codes.AlreadyExists || status.Code(err) == codes.FailedPrecondition ||
		status.Code(err) == codes.Aborted {
		return fmt.Errorf("%w: %v", ErrObjectPrecondition, err)
	}
	return err
}

var _ ObjectStore = (*GCSObjects)(nil)
