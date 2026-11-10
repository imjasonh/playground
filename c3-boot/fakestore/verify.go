package main

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"os"

	"github.com/sigstore/sigstore-go/pkg/bundle"
	"github.com/sigstore/sigstore-go/pkg/root"
	"github.com/sigstore/sigstore-go/pkg/verify"
)

func runVerify(args []string, stdout, stderr io.Writer) error {
	fs := flag.NewFlagSet("verify", flag.ContinueOnError)
	fs.SetOutput(stderr)
	trustedRootPath := fs.String("trusted-root", "", "trusted_root.json to verify against (required)")
	bundlePath := fs.String("bundle", "", "bundle JSON to verify (required)")
	artifactPath := fs.String("artifact", "", "signed file (required)")
	issuer := fs.String("issuer", defaultIssuer, "OIDC issuer that the certificate must name exactly")
	buildSignerURI := fs.String("build-signer-uri", defaultBuildSignerURI, "SAN URI that the certificate must name exactly")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("verify: unexpected arguments %q", fs.Args())
	}
	if *trustedRootPath == "" || *bundlePath == "" || *artifactPath == "" {
		return errors.New("verify: -trusted-root, -bundle, and -artifact are required")
	}
	f, err := os.Open(*artifactPath)
	if err != nil {
		return err
	}
	defer f.Close()
	if err := verifyBundle(*trustedRootPath, *bundlePath, f, *issuer, *buildSignerURI); err != nil {
		return err
	}
	fmt.Fprintln(stdout, "OK")
	return nil
}

// verifyBundle verifies a bundle for artifact with sigstore-go. It requires
// one RFC 3161 timestamp, one transparency log entry, and one SCT, and a
// certificate whose issuer and SAN URI equal issuer and san.
func verifyBundle(trustedRootPath, bundlePath string, artifact io.Reader, issuer, san string) error {
	tr, err := root.NewTrustedRootFromPath(trustedRootPath)
	if err != nil {
		return fmt.Errorf("loading trusted root: %w", err)
	}
	b, err := bundle.LoadJSONFromPath(bundlePath)
	if err != nil {
		return fmt.Errorf("loading bundle: %w", err)
	}
	v, err := verify.NewVerifier(tr,
		verify.WithSignedTimestamps(1),
		verify.WithTransparencyLog(1),
		verify.WithSignedCertificateTimestamps(1),
	)
	if err != nil {
		return err
	}
	id, err := verify.NewShortCertificateIdentity(issuer, "", san, "")
	if err != nil {
		return err
	}
	if _, err := v.Verify(b, verify.NewPolicy(verify.WithArtifact(artifact), verify.WithCertificateIdentity(id))); err != nil {
		return fmt.Errorf("verifying bundle: %w", err)
	}
	return nil
}
