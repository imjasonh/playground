package snapshot

import (
	"context"
	"fmt"
	"strings"

	kms "cloud.google.com/go/kms/apiv1"
	kmspb "cloud.google.com/go/kms/apiv1/kmspb"
)

// KeyWrapper wraps a serialized per-snapshot Tink keyset. Implementations must
// authenticate the supplied tenant/app/generation/snapshot associated data.
type KeyWrapper interface {
	Wrap(context.Context, []byte, []byte) ([]byte, error)
	Unwrap(context.Context, []byte, []byte) ([]byte, error)
	Close() error
}

type CloudKMSWrapper struct {
	keyName string
	client  *kms.KeyManagementClient
}

func NewCloudKMSWrapper(ctx context.Context, keyName string) (*CloudKMSWrapper, error) {
	if !strings.HasPrefix(keyName, "projects/") || !strings.Contains(keyName, "/cryptoKeys/") {
		return nil, fmt.Errorf("full Cloud KMS CryptoKey resource name is required")
	}
	client, err := kms.NewKeyManagementClient(ctx)
	if err != nil {
		return nil, err
	}
	return &CloudKMSWrapper{keyName: keyName, client: client}, nil
}

func (k *CloudKMSWrapper) Wrap(ctx context.Context, plaintext, aad []byte) ([]byte, error) {
	if len(plaintext) == 0 || len(aad) == 0 {
		return nil, fmt.Errorf("keyset plaintext and associated data are required")
	}
	response, err := k.client.Encrypt(ctx, &kmspb.EncryptRequest{
		Name: k.keyName, Plaintext: plaintext, AdditionalAuthenticatedData: aad,
	})
	if err != nil {
		return nil, fmt.Errorf("Cloud KMS wrap snapshot keyset: %w", err)
	}
	return response.Ciphertext, nil
}

func (k *CloudKMSWrapper) Unwrap(ctx context.Context, ciphertext, aad []byte) ([]byte, error) {
	if len(ciphertext) == 0 || len(aad) == 0 {
		return nil, fmt.Errorf("wrapped keyset and associated data are required")
	}
	response, err := k.client.Decrypt(ctx, &kmspb.DecryptRequest{
		Name: k.keyName, Ciphertext: ciphertext, AdditionalAuthenticatedData: aad,
	})
	if err != nil {
		return nil, fmt.Errorf("Cloud KMS unwrap snapshot keyset: %w", err)
	}
	return response.Plaintext, nil
}

func (k *CloudKMSWrapper) Close() error {
	if k == nil || k.client == nil {
		return nil
	}
	return k.client.Close()
}

var _ KeyWrapper = (*CloudKMSWrapper)(nil)
