// Package symbolizer resolves ESP32-C3 program counter (PC) hotspot addresses
// to function names and source file:line locations using Go's standard debug/elf
// and debug/dwarf packages, lazy-fetching symbolized ELF layers from GHCR by
// firmware elf_sha256 (or latest).
package symbolizer

import (
	"bytes"
	"compress/gzip"
	"context"
	"debug/dwarf"
	"debug/elf"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/xiao-otel/internal/otlp"
)

const (
	// ELFMediaTypeGzip is the OCI layer media type for gzipped symbolized ELFs in GHCR.
	ELFMediaTypeGzip = "application/vnd.xiao.esp32c3.elf.v1+gzip"
	// ELFMediaTypeRaw is an uncompressed ELF layer media type.
	ELFMediaTypeRaw = "application/x-elf"

	defaultRegistryBaseURL = "https://ghcr.io"
	maxELFBytes            = 32 * 1024 * 1024
	negativeCacheTTL       = 5 * time.Minute
	maxCachedTables        = 4
)

// Symbol is a resolved PC location.
type Symbol struct {
	Function string `json:"function,omitempty"`
	File     string `json:"file,omitempty"`
	Line     int    `json:"line,omitempty"`
}

// String returns a human-readable `function (file:line)` representation.
func (s Symbol) String() string {
	switch {
	case s.Function != "" && s.File != "" && s.Line > 0:
		return s.Function + " (" + s.File + ":" + strconv.Itoa(s.Line) + ")"
	case s.Function != "":
		return s.Function
	case s.File != "" && s.Line > 0:
		return s.File + ":" + strconv.Itoa(s.Line)
	default:
		return ""
	}
}

type funcRange struct {
	start uint64
	end   uint64
	name  string
}

type lineEntry struct {
	addr uint64
	file string
	line int
}

// Table is a parsed, immutable symbol + line-table index for one ELF binary.
type Table struct {
	funcs []funcRange
	lines []lineEntry
}

// ParseELF parses an uncompressed ELF binary into a fast lookup Table.
func ParseELF(raw []byte) (*Table, error) {
	f, err := elf.NewFile(bytes.NewReader(raw))
	if err != nil {
		return nil, fmt.Errorf("parse ELF: %w", err)
	}
	defer f.Close()

	var funcs []funcRange
	if syms, err := f.Symbols(); err == nil {
		funcs = make([]funcRange, 0, len(syms)/2)
		for _, sym := range syms {
			if elf.ST_TYPE(sym.Info) != elf.STT_FUNC || sym.Value == 0 || sym.Name == "" {
				continue
			}
			end := sym.Value + sym.Size
			if sym.Size == 0 {
				end = sym.Value + 4
			}
			funcs = append(funcs, funcRange{
				start: sym.Value,
				end:   end,
				name:  sym.Name,
			})
		}
		sort.Slice(funcs, func(i, j int) bool {
			return funcs[i].start < funcs[j].start
		})
	}

	var lines []lineEntry
	if d, err := f.DWARF(); err == nil {
		lines = parseDWARFLines(d)
	}

	if len(funcs) == 0 && len(lines) == 0 {
		return nil, errors.New("ELF contains neither .symtab functions nor DWARF line tables")
	}
	return &Table{funcs: funcs, lines: lines}, nil
}

func parseDWARFLines(d *dwarf.Data) []lineEntry {
	var out []lineEntry
	r := d.Reader()
	for {
		cu, err := r.Next()
		if err != nil || cu == nil {
			break
		}
		if cu.Tag != dwarf.TagCompileUnit {
			r.SkipChildren()
			continue
		}
		lr, err := d.LineReader(cu)
		if err != nil || lr == nil {
			r.SkipChildren()
			continue
		}
		var le dwarf.LineEntry
		for {
			if err := lr.Next(&le); err != nil {
				break
			}
			if le.EndSequence || le.Address == 0 || le.File == nil {
				continue
			}
			out = append(out, lineEntry{
				addr: le.Address,
				file: shortenSourcePath(le.File.Name),
				line: le.Line,
			})
		}
		r.SkipChildren()
	}
	sort.Slice(out, func(i, j int) bool {
		return out[i].addr < out[j].addr
	})
	return out
}

func shortenSourcePath(p string) string {
	clean := filepath.ToSlash(p)
	for _, marker := range []string{"/xiao-esp32c3/", "/src/"} {
		if idx := strings.LastIndex(clean, marker); idx >= 0 {
			return strings.TrimPrefix(clean[idx+1:], "/")
		}
	}
	parts := strings.Split(clean, "/")
	if len(parts) > 2 {
		return strings.Join(parts[len(parts)-2:], "/")
	}
	return clean
}

// Resolve looks up a PC address in the symbol and DWARF line tables.
func (t *Table) Resolve(pc uint64) (Symbol, bool) {
	if t == nil || pc == 0 {
		return Symbol{}, false
	}
	var out Symbol
	if len(t.funcs) > 0 {
		idx := sort.Search(len(t.funcs), func(i int) bool {
			return t.funcs[i].start > pc
		}) - 1
		if idx >= 0 && pc >= t.funcs[idx].start && pc < t.funcs[idx].end {
			out.Function = t.funcs[idx].name
		}
	}
	if len(t.lines) > 0 {
		idx := sort.Search(len(t.lines), func(i int) bool {
			return t.lines[i].addr > pc
		}) - 1
		if idx >= 0 && pc-t.lines[idx].addr <= 4096 {
			out.File = t.lines[idx].file
			out.Line = t.lines[idx].line
		}
	}
	if out.Function == "" && out.File == "" {
		return Symbol{}, false
	}
	return out, true
}

type cacheEntry struct {
	table    *Table
	failedAt time.Time
}

// Symbolizer resolves firmware PC hotspots using a local ELF file or GHCR OCI ELF layers.
type Symbolizer struct {
	Repo            string
	RegistryBaseURL string
	LocalELFPath    string
	HTTPClient      *http.Client
	Now             func() time.Time

	mu    sync.Mutex
	cache map[string]cacheEntry
}

// EnrichSpans resolves `pc.hotspot` events on the given spans in place, adding
// `function`, `file`, and `line` attributes before export, and returns the map
// of resolved hex PC strings to Symbol.
func (s *Symbolizer) EnrichSpans(ctx context.Context, spans []otlp.Span) map[string]Symbol {
	if s == nil {
		return nil
	}
	// Check whether any span contains pc.hotspot events and extract elf_sha256 if present.
	elfTag := ""
	hasHotspots := false
	for i := range spans {
		if v, ok := spans[i].Attributes["mcu.elf_sha256"].(string); ok && v != "" && elfTag == "" {
			elfTag = strings.ToLower(strings.TrimSpace(v))
		}
		for j := range spans[i].Events {
			if spans[i].Events[j].Name == "pc.hotspot" {
				hasHotspots = true
			}
		}
	}
	if !hasHotspots {
		return nil
	}
	if elfTag == "" {
		elfTag = "latest"
	}

	tbl := s.tableForTag(ctx, elfTag)
	if tbl == nil {
		return nil
	}

	resolved := make(map[string]Symbol)
	for i := range spans {
		for j := range spans[i].Events {
			ev := &spans[i].Events[j]
			if ev.Name != "pc.hotspot" {
				continue
			}
			pcStr, ok := ev.Attributes["pc"].(string)
			if !ok {
				continue
			}
			pc, err := parseHexPC(pcStr)
			if err != nil {
				continue
			}
			sym, found := tbl.Resolve(pc)
			if !found {
				continue
			}
			if ev.Attributes == nil {
				ev.Attributes = make(map[string]any, 4)
			}
			if sym.Function != "" {
				ev.Attributes["function"] = sym.Function
			}
			if sym.File != "" {
				ev.Attributes["file"] = sym.File
			}
			if sym.Line > 0 {
				ev.Attributes["line"] = int64(sym.Line)
			}
			resolved[pcStr] = sym
		}
	}
	return resolved
}

func parseHexPC(raw string) (uint64, error) {
	trimmed := strings.TrimSpace(raw)
	trimmed = strings.TrimPrefix(trimmed, "0x")
	trimmed = strings.TrimPrefix(trimmed, "0X")
	return strconv.ParseUint(trimmed, 16, 64)
}

func (s *Symbolizer) now() time.Time {
	if s.Now != nil {
		return s.Now()
	}
	return time.Now()
}

func (s *Symbolizer) tableForTag(ctx context.Context, tag string) *Table {
	s.mu.Lock()
	if s.cache == nil {
		s.cache = make(map[string]cacheEntry)
	}
	if entry, ok := s.cache[tag]; ok {
		if entry.table != nil {
			s.mu.Unlock()
			return entry.table
		}
		if s.now().Sub(entry.failedAt) < negativeCacheTTL {
			s.mu.Unlock()
			return nil
		}
	}
	s.mu.Unlock()

	var tbl *Table
	var err error
	if s.LocalELFPath != "" {
		tbl, err = loadLocalELF(s.LocalELFPath)
	} else if s.Repo != "" {
		tbl, err = s.fetchFromGHCR(ctx, tag)
		if err != nil && tag != "latest" {
			tbl, err = s.fetchFromGHCR(ctx, "latest")
		}
	}

	s.mu.Lock()
	defer s.mu.Unlock()
	if err != nil || tbl == nil {
		s.cache[tag] = cacheEntry{failedAt: s.now()}
		return nil
	}
	if len(s.cache) >= maxCachedTables {
		clear(s.cache)
	}
	s.cache[tag] = cacheEntry{table: tbl}
	return tbl
}

func loadLocalELF(path string) (*Table, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return ParseELF(raw)
}

func (s *Symbolizer) fetchFromGHCR(ctx context.Context, tag string) (*Table, error) {
	base := strings.TrimRight(s.RegistryBaseURL, "/")
	if base == "" {
		base = defaultRegistryBaseURL
	}
	client := s.HTTPClient
	if client == nil {
		client = &http.Client{Timeout: 10 * time.Second}
	}

	// 1. Fetch anonymous pull token.
	tokURL := fmt.Sprintf("%s/token?scope=repository:%s:pull", base, s.Repo)
	tokReq, err := http.NewRequestWithContext(ctx, http.MethodGet, tokURL, nil)
	if err != nil {
		return nil, err
	}
	tokResp, err := client.Do(tokReq)
	if err != nil {
		return nil, err
	}
	defer tokResp.Body.Close()
	if tokResp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("GHCR token HTTP %d", tokResp.StatusCode)
	}
	var tokBody struct {
		Token string `json:"token"`
	}
	if err := json.NewDecoder(io.LimitReader(tokResp.Body, 16*1024)).Decode(&tokBody); err != nil || tokBody.Token == "" {
		return nil, errors.New("decode GHCR token")
	}

	// 2. Fetch OCI manifest for tag.
	manURL := fmt.Sprintf("%s/v2/%s/manifests/%s", base, s.Repo, tag)
	manReq, err := http.NewRequestWithContext(ctx, http.MethodGet, manURL, nil)
	if err != nil {
		return nil, err
	}
	manReq.Header.Set("Authorization", "Bearer "+tokBody.Token)
	manReq.Header.Set("Accept", "application/vnd.oci.image.manifest.v1+json, application/vnd.docker.distribution.manifest.v2+json")
	manResp, err := client.Do(manReq)
	if err != nil {
		return nil, err
	}
	defer manResp.Body.Close()
	if manResp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("GHCR manifest HTTP %d", manResp.StatusCode)
	}
	var manifest struct {
		Layers []struct {
			MediaType string `json:"mediaType"`
			Digest    string `json:"digest"`
		} `json:"layers"`
	}
	if err := json.NewDecoder(io.LimitReader(manResp.Body, 64*1024)).Decode(&manifest); err != nil {
		return nil, err
	}

	var elfDigest string
	var gzipped bool
	for _, layer := range manifest.Layers {
		switch layer.MediaType {
		case ELFMediaTypeGzip:
			elfDigest = layer.Digest
			gzipped = true
		case ELFMediaTypeRaw:
			elfDigest = layer.Digest
			gzipped = false
		}
		if elfDigest != "" {
			break
		}
	}
	if elfDigest == "" {
		return nil, errors.New("manifest contains no ELF symbol layer")
	}

	// 3. Download ELF blob.
	blobURL := fmt.Sprintf("%s/v2/%s/blobs/%s", base, s.Repo, elfDigest)
	blobReq, err := http.NewRequestWithContext(ctx, http.MethodGet, blobURL, nil)
	if err != nil {
		return nil, err
	}
	blobReq.Header.Set("Authorization", "Bearer "+tokBody.Token)
	blobResp, err := client.Do(blobReq)
	if err != nil {
		return nil, err
	}
	defer blobResp.Body.Close()
	if blobResp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("GHCR blob HTTP %d", blobResp.StatusCode)
	}

	var reader io.Reader = io.LimitReader(blobResp.Body, maxELFBytes)
	if gzipped {
		gz, err := gzip.NewReader(reader)
		if err != nil {
			return nil, fmt.Errorf("gunzip ELF layer: %w", err)
		}
		defer gz.Close()
		reader = io.LimitReader(gz, maxELFBytes)
	}
	rawELF, err := io.ReadAll(reader)
	if err != nil {
		return nil, err
	}
	return ParseELF(rawELF)
}
