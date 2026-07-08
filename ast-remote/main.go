// Command ast-remote encodes/decodes source as AST payloads and runs
// storage / latency benchmarks against gzip(raw).
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"time"

	"github.com/imjasonh/playground/ast-remote/internal/codec"
	"github.com/imjasonh/playground/ast-remote/internal/langs"
)

func main() {
	if len(os.Args) < 2 {
		usage()
		os.Exit(2)
	}
	switch os.Args[1] {
	case "encode":
		cmdEncode(os.Args[2:])
	case "decode":
		cmdDecode(os.Args[2:])
	case "bench":
		cmdBench(os.Args[2:])
	case "bench-remote":
		cmdBenchRemote(os.Args[2:])
	case "languages":
		for _, n := range langs.Names() {
			fmt.Println(n)
		}
	case "help", "-h", "--help":
		usage()
	default:
		fmt.Fprintf(os.Stderr, "unknown command %q\n", os.Args[1])
		usage()
		os.Exit(2)
	}
}

func usage() {
	fmt.Fprintf(os.Stderr, `ast-remote — AST-compressed git remote tooling

Usage:
  ast-remote encode [flags] <file>         encode one file; print size stats
  ast-remote decode --encoding=E <file>    decode payload from file to stdout
  ast-remote bench [flags] <repo-or-dir>   benchmark leaf-AST vs full-AST vs gzip
  ast-remote languages                     list supported languages

Encode flags:
  -o FILE         write chosen payload to file
  -full-tree      store AST1 full flattened tree (usually larger)
  -leaves         store AST1 leaf-stream (legacy; usually larger)
  -no-adaptive    always store AST subst form (skip dict/gzip min)

Bench flags:
  -out FILE       write JSON results to FILE
  -repeat N       repeat encode/decode timing (default 3)
  -limit N        max source files to include (0 = all)
  -no-adaptive    force AST subst storage (disable adaptive min)

  ast-remote bench-remote [flags] <dir>    push/fetch wall time vs file:// remote
    -repeat N     repeats (default 3)
    -helper PATH  path to git-remote-ast (default ./git-remote-ast)
`)
}

func cmdEncode(args []string) {
	fs := flag.NewFlagSet("encode", flag.ExitOnError)
	outPath := fs.String("o", "", "write payload to file")
	full := fs.Bool("full-tree", false, "prefer AST1 full tree")
	leaves := fs.Bool("leaves", false, "prefer AST1 leaf stream")
	noAdapt := fs.Bool("no-adaptive", false, "disable adaptive min (force AST subst)")
	fs.Parse(args)
	if fs.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "encode requires one file")
		os.Exit(2)
	}
	path := fs.Arg(0)
	src, err := os.ReadFile(path)
	must(err)
	res, err := codec.EncodeFileOpts(path, src, codec.EncodeOptions{
		PreferFullTree:      *full,
		PreferLeaves:        *leaves,
		AlsoMeasureFullTree: true,
		NoAdaptive:          *noAdapt,
	})
	must(err)
	fmt.Printf("path:       %s\n", path)
	fmt.Printf("lang:       %s\n", res.Lang)
	fmt.Printf("encoding:   %s (mode=%s)\n", res.Encoding, res.Mode)
	fmt.Printf("raw:        %d bytes\n", res.RawSize)
	fmt.Printf("gzip(raw):  %d bytes\n", res.GzipRawSize)
	if res.LeafASTSize > 0 {
		fmt.Printf("subst+gzip: %d bytes (%.1f%% of gzip)\n", res.LeafASTSize, pct(res.LeafASTSize, res.GzipRawSize))
	}
	if res.RawDictSize > 0 {
		fmt.Printf("raw+dict:   %d bytes (%.1f%% of gzip)\n", res.RawDictSize, pct(res.RawDictSize, res.GzipRawSize))
	}
	if res.ASTDictSize > 0 {
		fmt.Printf("subst+dict: %d bytes (%.1f%% of gzip)\n", res.ASTDictSize, pct(res.ASTDictSize, res.GzipRawSize))
	}
	if res.FullASTSize > 0 {
		fmt.Printf("full+gzip:  %d bytes (%.1f%% of gzip)\n", res.FullASTSize, pct(res.FullASTSize, res.GzipRawSize))
	}
	fmt.Printf("stored:     %d bytes (%.1f%% of raw, %.1f%% of gzip)\n",
		res.PayloadSize,
		pct(res.PayloadSize, res.RawSize),
		pct(res.PayloadSize, res.GzipRawSize))
	if res.NodeCount > 0 {
		fmt.Printf("nodes:      %d\n", res.NodeCount)
		if res.StringCount > 0 {
			fmt.Printf("strings:    %d\n", res.StringCount)
		}
	}
	if res.SkippedReason != "" {
		fmt.Printf("note:       %s\n", res.SkippedReason)
	}
	if *outPath != "" {
		must(os.WriteFile(*outPath, res.Payload, 0o644))
	}
	back, err := codec.Decode(res.Encoding, res.Payload)
	must(err)
	if string(back) != string(src) {
		fmt.Fprintln(os.Stderr, "ROUND-TRIP MISMATCH")
		os.Exit(1)
	}
	fmt.Println("round-trip: ok")
}

func cmdDecode(args []string) {
	fs := flag.NewFlagSet("decode", flag.ExitOnError)
	enc := fs.String("encoding", codec.EncodingASTGzip, "payload encoding")
	fs.Parse(args)
	if fs.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "decode requires one file")
		os.Exit(2)
	}
	payload, err := os.ReadFile(fs.Arg(0))
	must(err)
	out, err := codec.Decode(*enc, payload)
	must(err)
	_, _ = os.Stdout.Write(out)
}

// FileStat is per-file benchmark data.
type FileStat struct {
	Path           string  `json:"path"`
	Lang           string  `json:"lang"`
	Encoding       string  `json:"encoding"`
	Mode           string  `json:"mode"`
	RawBytes       int     `json:"raw_bytes"`
	GzipBytes      int     `json:"gzip_bytes"`
	LeafASTBytes   int     `json:"leaf_ast_bytes"` // AST2 subst+gzip
	RawDictBytes   int     `json:"raw_dict_bytes"`
	ASTDictBytes   int     `json:"ast_dict_bytes"`
	FullASTBytes   int     `json:"full_ast_bytes"`
	StoredBytes    int     `json:"stored_bytes"`
	LeafVsGzip     float64 `json:"leaf_vs_gzip_pct"`
	RawDictVsGzip  float64 `json:"raw_dict_vs_gzip_pct"`
	FullVsGzip     float64 `json:"full_vs_gzip_pct"`
	StoredVsGzip   float64 `json:"stored_vs_gzip_pct"`
	EncodeMs       float64 `json:"encode_ms"`
	DecodeMs       float64 `json:"decode_ms"`
	GzipEncodeMs   float64 `json:"gzip_encode_ms"`
	GzipDecodeMs   float64 `json:"gzip_decode_ms"`
	SkippedReason  string  `json:"skipped_reason,omitempty"`
}

// BenchReport is the JSON document written by `ast-remote bench`.
type BenchReport struct {
	GeneratedAt string     `json:"generated_at"`
	GoVersion   string     `json:"go_version"`
	Source      string     `json:"source"`
	Files       []FileStat `json:"files"`
	Summary     Summary    `json:"summary"`
}

// Summary aggregates across files.
type Summary struct {
	Files             int     `json:"files"`
	ASTStored         int     `json:"ast_stored"`
	DictStored        int     `json:"dict_stored"`
	GzipFallback      int     `json:"gzip_fallback"`
	TotalRaw          int64   `json:"total_raw_bytes"`
	TotalGzip         int64   `json:"total_gzip_bytes"`
	TotalLeafAST      int64   `json:"total_leaf_ast_bytes"`
	TotalRawDict      int64   `json:"total_raw_dict_bytes"`
	TotalASTDict      int64   `json:"total_ast_dict_bytes"`
	TotalFullAST      int64   `json:"total_full_ast_bytes"`
	TotalStored       int64   `json:"total_stored_bytes"`
	LeafVsGzipPct     float64 `json:"leaf_vs_gzip_pct"`
	RawDictVsGzipPct  float64 `json:"raw_dict_vs_gzip_pct"`
	FullVsGzipPct     float64 `json:"full_vs_gzip_pct"`
	StoredVsGzipPct   float64 `json:"stored_vs_gzip_pct"`
	MedianLeafVsGzip  float64 `json:"median_leaf_vs_gzip_pct"`
	MeanEncodeMs      float64 `json:"mean_encode_ms"`
	MeanDecodeMs      float64 `json:"mean_decode_ms"`
	MeanGzipEncodeMs  float64 `json:"mean_gzip_encode_ms"`
	MeanGzipDecodeMs  float64 `json:"mean_gzip_decode_ms"`
	Verdict           string  `json:"verdict"`
}

func cmdBench(args []string) {
	fs := flag.NewFlagSet("bench", flag.ExitOnError)
	outPath := fs.String("out", "", "write JSON report")
	repeat := fs.Int("repeat", 3, "timing repeats")
	limit := fs.Int("limit", 0, "max files (0=all)")
	noAdapt := fs.Bool("no-adaptive", false, "force AST storage")
	fs.Parse(args)
	if fs.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "bench requires a directory or git repo path")
		os.Exit(2)
	}
	root := fs.Arg(0)
	files, err := collectSourceFiles(root)
	must(err)
	if *limit > 0 && len(files) > *limit {
		files = files[:*limit]
	}
	if len(files) == 0 {
		fmt.Fprintln(os.Stderr, "no supported source files found")
		os.Exit(1)
	}

	report := BenchReport{
		GeneratedAt: time.Now().UTC().Format(time.RFC3339),
		GoVersion:   runtime.Version(),
		Source:      root,
	}

	var leafRatios []float64
	for _, path := range files {
		src, err := os.ReadFile(path)
		if err != nil {
			fmt.Fprintf(os.Stderr, "skip %s: %v\n", path, err)
			continue
		}
		rel := path
		if r, err := filepath.Rel(root, path); err == nil {
			rel = r
		}

		var encMs, decMs, gzEncMs, gzDecMs float64
		var last *codec.Result
		opts := codec.EncodeOptions{
			AlsoMeasureFullTree: true,
			NoAdaptive:          *noAdapt,
		}
		for i := 0; i < *repeat; i++ {
			t0 := time.Now()
			res, err := codec.EncodeFileOpts(path, src, opts)
			must(err)
			encMs += float64(time.Since(t0).Microseconds()) / 1000.0
			last = res

			t1 := time.Now()
			back, err := codec.Decode(res.Encoding, res.Payload)
			must(err)
			decMs += float64(time.Since(t1).Microseconds()) / 1000.0
			if string(back) != string(src) {
				must(fmt.Errorf("round-trip mismatch on %s", path))
			}

			t2 := time.Now()
			gzPayload := mustGzip(src)
			gzEncMs += float64(time.Since(t2).Microseconds()) / 1000.0
			t3 := time.Now()
			_, err = codec.Decode(codec.EncodingRaw, gzPayload)
			must(err)
			gzDecMs += float64(time.Since(t3).Microseconds()) / 1000.0
		}
		n := float64(*repeat)
		fs := FileStat{
			Path:          rel,
			Lang:          last.Lang,
			Encoding:      last.Encoding,
			Mode:          last.Mode,
			RawBytes:      last.RawSize,
			GzipBytes:     last.GzipRawSize,
			LeafASTBytes:  last.LeafASTSize,
			RawDictBytes:  last.RawDictSize,
			ASTDictBytes:  last.ASTDictSize,
			FullASTBytes:  last.FullASTSize,
			StoredBytes:   last.PayloadSize,
			LeafVsGzip:    pct(last.LeafASTSize, last.GzipRawSize),
			RawDictVsGzip: pct(last.RawDictSize, last.GzipRawSize),
			FullVsGzip:    pct(last.FullASTSize, last.GzipRawSize),
			StoredVsGzip:  pct(last.PayloadSize, last.GzipRawSize),
			EncodeMs:      encMs / n,
			DecodeMs:      decMs / n,
			GzipEncodeMs:  gzEncMs / n,
			GzipDecodeMs:  gzDecMs / n,
			SkippedReason: last.SkippedReason,
		}
		report.Files = append(report.Files, fs)
		if last.LeafASTSize > 0 && last.GzipRawSize > 0 {
			leafRatios = append(leafRatios, fs.LeafVsGzip)
		}
	}

	report.Summary = summarize(report.Files, leafRatios)
	printSummary(report)

	if *outPath != "" {
		b, err := json.MarshalIndent(report, "", "  ")
		must(err)
		must(os.WriteFile(*outPath, append(b, '\n'), 0o644))
		fmt.Printf("\nwrote %s\n", *outPath)
	}
}

func summarize(files []FileStat, leafRatios []float64) Summary {
	s := Summary{Files: len(files)}
	var enc, dec, gzEnc, gzDec float64
	for _, f := range files {
		s.TotalRaw += int64(f.RawBytes)
		s.TotalGzip += int64(f.GzipBytes)
		s.TotalLeafAST += int64(f.LeafASTBytes)
		s.TotalRawDict += int64(f.RawDictBytes)
		s.TotalASTDict += int64(f.ASTDictBytes)
		s.TotalFullAST += int64(f.FullASTBytes)
		s.TotalStored += int64(f.StoredBytes)
		enc += f.EncodeMs
		dec += f.DecodeMs
		gzEnc += f.GzipEncodeMs
		gzDec += f.GzipDecodeMs
		switch f.Encoding {
		case codec.EncodingASTGzip, codec.EncodingASTDict:
			s.ASTStored++
		case codec.EncodingRawDict:
			s.DictStored++
		default:
			s.GzipFallback++
		}
	}
	if s.Files > 0 {
		n := float64(s.Files)
		s.MeanEncodeMs = enc / n
		s.MeanDecodeMs = dec / n
		s.MeanGzipEncodeMs = gzEnc / n
		s.MeanGzipDecodeMs = gzDec / n
	}
	s.LeafVsGzipPct = pct64(s.TotalLeafAST, s.TotalGzip)
	s.RawDictVsGzipPct = pct64(s.TotalRawDict, s.TotalGzip)
	s.FullVsGzipPct = pct64(s.TotalFullAST, s.TotalGzip)
	s.StoredVsGzipPct = pct64(s.TotalStored, s.TotalGzip)
	if len(leafRatios) > 0 {
		sort.Float64s(leafRatios)
		s.MedianLeafVsGzip = leafRatios[len(leafRatios)/2]
	}
	switch {
	case s.StoredVsGzipPct < 95:
		s.Verdict = "adaptive AST/dict store beats plain gzip on total bytes for this corpus"
	case s.StoredVsGzipPct <= 100.5:
		s.Verdict = "adaptive AST/dict store is at or under plain gzip"
	default:
		s.Verdict = "adaptive store still larger than gzip (unexpected)"
	}
	if s.LeafVsGzipPct > 0 && s.LeafVsGzipPct < 105 {
		s.Verdict += "; AST2 subst+gzip is near parity with gzip alone"
	}
	if s.RawDictVsGzipPct > 0 && s.RawDictVsGzipPct < 100 {
		s.Verdict += fmt.Sprintf("; fixed lang dict alone is %.1f%% of gzip", s.RawDictVsGzipPct)
	}
	return s
}

func printSummary(r BenchReport) {
	s := r.Summary
	fmt.Printf("Source:           %s\n", r.Source)
	fmt.Printf("Files:            %d (%d AST, %d dict, %d gzip)\n", s.Files, s.ASTStored, s.DictStored, s.GzipFallback)
	fmt.Printf("Total raw:        %d bytes\n", s.TotalRaw)
	fmt.Printf("Total gzip:       %d bytes (%.1f%% of raw)\n", s.TotalGzip, pct64(s.TotalGzip, s.TotalRaw))
	fmt.Printf("Total subst+gzip: %d bytes (%.1f%% of gzip)\n", s.TotalLeafAST, s.LeafVsGzipPct)
	if s.TotalRawDict > 0 {
		fmt.Printf("Total raw+dict:   %d bytes (%.1f%% of gzip)\n", s.TotalRawDict, s.RawDictVsGzipPct)
	}
	if s.TotalASTDict > 0 {
		fmt.Printf("Total subst+dict: %d bytes (%.1f%% of gzip)\n", s.TotalASTDict, pct64(s.TotalASTDict, s.TotalGzip))
	}
	if s.TotalFullAST > 0 {
		fmt.Printf("Total full+gzip:  %d bytes (%.1f%% of gzip)\n", s.TotalFullAST, s.FullVsGzipPct)
	}
	fmt.Printf("Total stored:     %d bytes (%.1f%% of gzip) [adaptive min]\n", s.TotalStored, s.StoredVsGzipPct)
	fmt.Printf("Median subst/gzip:%.1f%%\n", s.MedianLeafVsGzip)
	fmt.Printf("Mean encode:      AST %.2f ms  vs gzip %.2f ms\n", s.MeanEncodeMs, s.MeanGzipEncodeMs)
	fmt.Printf("Mean decode:      AST %.2f ms  vs gzip %.2f ms\n", s.MeanDecodeMs, s.MeanGzipDecodeMs)
	fmt.Printf("Verdict:          %s\n", s.Verdict)
}

func collectSourceFiles(root string) ([]string, error) {
	info, err := os.Stat(root)
	if err != nil {
		return nil, err
	}
	var out []string
	if !info.IsDir() {
		if langs.IsSourcePath(root) {
			return []string{root}, nil
		}
		return nil, fmt.Errorf("%s is not a supported source file", root)
	}
	skip := map[string]bool{
		".git": true, "node_modules": true, "target": true, "vendor": true,
	}
	err = filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		name := d.Name()
		if d.IsDir() {
			if skip[name] || (strings.HasPrefix(name, ".") && path != root) {
				return filepath.SkipDir
			}
			return nil
		}
		if langs.IsSourcePath(path) {
			out = append(out, path)
		}
		return nil
	})
	sort.Strings(out)
	return out, err
}

func mustGzip(b []byte) []byte {
	res, err := codec.EncodeFile("file.bin", b)
	must(err)
	return res.Payload
}

func pct(a, b int) float64 {
	if b == 0 {
		return 0
	}
	return 100 * float64(a) / float64(b)
}

func pct64(a, b int64) float64 {
	if b == 0 {
		return 0
	}
	return 100 * float64(a) / float64(b)
}

func must(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func cmdBenchRemote(args []string) {
	fs := flag.NewFlagSet("bench-remote", flag.ExitOnError)
	repeat := fs.Int("repeat", 3, "repeats")
	helperPath := fs.String("helper", "./git-remote-ast", "path to git-remote-ast binary")
	fs.Parse(args)
	if fs.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "bench-remote requires a source directory to commit")
		os.Exit(2)
	}
	srcDir := fs.Arg(0)

	absHelper, err := filepath.Abs(*helperPath)
	must(err)
	if _, err := os.Stat(absHelper); err != nil {
		must(fmt.Errorf("build git-remote-ast first (%s): %w", absHelper, err))
	}

	tmp, err := os.MkdirTemp("", "ast-remote-bench-*")
	must(err)
	defer os.RemoveAll(tmp)

	repo := filepath.Join(tmp, "repo")
	must(runCmd(tmp, nil, "git", "init", "-b", "main", repo))
	must(runCmd(repo, nil, "git", "config", "user.email", "bench@example.com"))
	must(runCmd(repo, nil, "git", "config", "user.name", "Bench"))
	must(copyFlatSources(srcDir, repo))
	dateEnv := append(os.Environ(),
		"GIT_AUTHOR_DATE=2020-01-01T00:00:00",
		"GIT_COMMITTER_DATE=2020-01-01T00:00:00",
	)
	must(runCmd(repo, nil, "git", "add", "-A"))
	must(runCmd(repo, dateEnv, "git", "commit", "-m", "bench"))

	astStore := filepath.Join(tmp, "ast-store")
	plainRemote := filepath.Join(tmp, "plain.git")

	helperDir := filepath.Dir(absHelper)
	pathEnv := append(os.Environ(), "PATH="+helperDir+string(os.PathListSeparator)+os.Getenv("PATH"))

	var astPush, astFetch, plainPush, plainFetch time.Duration
	for i := 0; i < *repeat; i++ {
		_ = os.RemoveAll(astStore)
		_ = os.RemoveAll(plainRemote)
		must(runCmd(tmp, nil, "git", "init", "--bare", plainRemote))

		t0 := time.Now()
		must(runCmd(repo, pathEnv, "git", "push", "ast::"+astStore, "main"))
		astPush += time.Since(t0)

		cloneAst := filepath.Join(tmp, fmt.Sprintf("clone-ast-%d", i))
		t1 := time.Now()
		must(runCmd(tmp, pathEnv, "git", "clone", "ast::"+astStore, cloneAst))
		astFetch += time.Since(t1)

		t2 := time.Now()
		must(runCmd(repo, nil, "git", "push", "file://"+plainRemote, "main"))
		plainPush += time.Since(t2)

		clonePlain := filepath.Join(tmp, fmt.Sprintf("clone-plain-%d", i))
		t3 := time.Now()
		must(runCmd(tmp, nil, "git", "clone", "file://"+plainRemote, clonePlain))
		plainFetch += time.Since(t3)
	}

	n := float64(*repeat)
	fmt.Printf("Source tree:     %s\n", srcDir)
	fmt.Printf("Repeats:         %d\n", *repeat)
	fmt.Printf("AST push:        %.1f ms (mean)\n", float64(astPush.Microseconds())/1000.0/n)
	fmt.Printf("AST fetch/clone: %.1f ms (mean)\n", float64(astFetch.Microseconds())/1000.0/n)
	fmt.Printf("file:// push:    %.1f ms (mean)\n", float64(plainPush.Microseconds())/1000.0/n)
	fmt.Printf("file:// clone:   %.1f ms (mean)\n", float64(plainFetch.Microseconds())/1000.0/n)
	fmt.Printf("Push ratio:      AST/plain = %.2fx\n", float64(astPush)/float64(plainPush))
	fmt.Printf("Fetch ratio:     AST/plain = %.2fx\n", float64(astFetch)/float64(plainFetch))
}

func runCmd(dir string, env []string, name string, args ...string) error {
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	if env != nil {
		cmd.Env = env
	}
	out, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("%s %v: %w\n%s", name, args, err, out)
	}
	return nil
}

func copyFlatSources(src, dst string) error {
	entries, err := os.ReadDir(src)
	if err != nil {
		return err
	}
	n := 0
	for _, e := range entries {
		if e.IsDir() {
			continue
		}
		in := filepath.Join(src, e.Name())
		data, err := os.ReadFile(in)
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(dst, e.Name()), data, 0o644); err != nil {
			return err
		}
		n++
	}
	if n == 0 {
		return fmt.Errorf("no files copied from %s", src)
	}
	return nil
}

var _ = io.Discard
