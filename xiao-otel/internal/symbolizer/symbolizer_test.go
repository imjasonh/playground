package symbolizer

import (
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/xiao-otel/internal/otlp"
)

func TestParseELFAndEnrichSpansFromGHCR(t *testing.T) {
	// Cross-compile a tiny RISC-V ELF with .symtab + DWARF .debug_line so the test
	// exercises real ELF/DWARF parsing deterministically on any host OS.
	tmpDir := t.TempDir()
	srcPath := filepath.Join(tmpDir, "main.go")
	elfPath := filepath.Join(tmpDir, "sample.elf")
	if err := os.WriteFile(srcPath, []byte("package main\nfunc main() { println(\"hi\") }\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "build", "-o", elfPath, srcPath)
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=riscv64", "CGO_ENABLED=0")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("go build sample RISC-V ELF failed: %v\n%s", err, string(out))
	}

	rawELF, err := os.ReadFile(elfPath)
	if err != nil {
		t.Fatal(err)
	}
	tbl, err := ParseELF(rawELF)
	if err != nil {
		t.Fatalf("ParseELF failed: %v", err)
	}
	var mainPC uint64
	for _, fn := range tbl.funcs {
		if fn.name == "main.main" {
			mainPC = fn.start
			break
		}
	}
	if mainPC == 0 {
		t.Fatalf("main.main not found in parsed ELF (%d funcs)", len(tbl.funcs))
	}

	var gzBuf bytes.Buffer
	gz := gzip.NewWriter(&gzBuf)
	if _, err := gz.Write(rawELF); err != nil {
		t.Fatal(err)
	}
	if err := gz.Close(); err != nil {
		t.Fatal(err)
	}
	gzBytes := gzBuf.Bytes()
	gzSum := sha256.Sum256(gzBytes)
	elfDigest := "sha256:" + hex.EncodeToString(gzSum[:])
	elfTag := strings.Repeat("a", 64)

	// Serve the gzipped ELF through a mock GHCR OCI registry.
	ghcr := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch {
		case strings.HasPrefix(r.URL.Path, "/token"):
			w.Header().Set("Content-Type", "application/json")
			_, _ = w.Write([]byte(`{"token":"test-tok"}`))
		case strings.HasSuffix(r.URL.Path, "/manifests/"+elfTag):
			w.Header().Set("Content-Type", "application/vnd.oci.image.manifest.v1+json")
			_, _ = w.Write([]byte(`{"layers":[{"mediaType":"application/octet-stream","digest":"sha256:` + strings.Repeat("b", 64) + `"},{"mediaType":"` + ELFMediaTypeGzip + `","digest":"` + elfDigest + `"}]}`))
		case strings.HasSuffix(r.URL.Path, "/blobs/"+elfDigest):
			w.Header().Set("Content-Type", ELFMediaTypeGzip)
			_, _ = w.Write(gzBytes)
		default:
			http.NotFound(w, r)
		}
	}))
	defer ghcr.Close()

	sym := &Symbolizer{
		Repo:            "imjasonh/playground/xiao-esp32c3",
		RegistryBaseURL: ghcr.URL,
		HTTPClient:      ghcr.Client(),
	}

	pcHex := fmt.Sprintf("0x%x", mainPC)
	spans := []otlp.Span{
		{
			TraceID:   "0123456789abcdef0123456789abcdef",
			SpanID:    "1111111111111111",
			Name:      "xiao.wake #1",
			StartTime: time.Now(),
			EndTime:   time.Now(),
			Attributes: map[string]any{
				"mcu.elf_sha256": elfTag,
			},
			Events: []otlp.SpanEvent{
				{
					Time: time.Now(),
					Name: "pc.hotspot",
					Attributes: map[string]any{
						"pc":   pcHex,
						"hits": int64(9),
					},
				},
			},
		},
	}

	resolved := sym.EnrichSpans(t.Context(), spans)
	got, ok := resolved[pcHex]
	if !ok {
		t.Fatalf("expected PC %s to resolve, got %+v", pcHex, resolved)
	}
	if got.Function != "main.main" {
		t.Fatalf("resolved function = %q, want main.main", got.Function)
	}
	if !strings.HasSuffix(got.File, "main.go") || got.Line <= 0 {
		t.Fatalf("expected main.go:line from DWARF, got %+v", got)
	}
	evAttrs := spans[0].Events[0].Attributes
	if evAttrs["function"] != "main.main" || evAttrs["file"] != got.File {
		t.Fatalf("span event attributes not enriched: %+v", evAttrs)
	}
}
