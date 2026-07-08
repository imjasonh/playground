// Command ast-remote encodes/decodes source with the protocol and runs
// storage / latency benchmarks against gzip(raw).
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net"
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
	fmt.Fprintf(os.Stderr, `ast-remote — protocol-compressed git remote tooling

Usage:
  ast-remote encode [flags] <file>         encode one file; print size stats
  ast-remote decode --encoding=E <file>    decode payload from file to stdout
  ast-remote bench [flags] <repo-or-dir>   benchmark protocol vs gzip (sizes)
  ast-remote bench-remote [flags] <dir>    full git clone wall time vs git-daemon
  ast-remote languages                     list supported languages

Encode flags:
  -o FILE         write chosen payload to file
  -no-adaptive    always store protocol+flate (skip dict/gzip min)

Bench flags:
  -out FILE       write JSON results to FILE
  -repeat N       repeat encode/decode timing (default 3)
  -limit N        max source files to include (0 = all)
  -no-adaptive    force protocol+flate storage (disable adaptive min)

bench-remote flags:
  -out FILE       write JSON results to FILE
  -repeat N       clone repeats (default 3)
  -commits N      synthetic history depth when <dir> is not a git repo (default 5)
  -depth N        for git repos: shallow to N commits (0 = full history)
  -ref REF        branch/ref to publish (default: HEAD of source repo)
  -helper PATH    path to git-remote-ast (default ./git-remote-ast)
  -port N         git-daemon listen port (default 0 = ephemeral)
  -skip-fsck      skip post-clone fsck (faster on huge repos)
`)
}

func cmdEncode(args []string) {
	fs := flag.NewFlagSet("encode", flag.ExitOnError)
	outPath := fs.String("o", "", "write payload to file")
	noAdapt := fs.Bool("no-adaptive", false, "disable adaptive min (force protocol+flate)")
	fs.Parse(args)
	if fs.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "encode requires one file")
		os.Exit(2)
	}
	path := fs.Arg(0)
	src, err := os.ReadFile(path)
	must(err)
	res, err := codec.EncodeFileOpts(path, src, codec.EncodeOptions{
		NoAdaptive: *noAdapt,
	})
	must(err)
	fmt.Printf("path:       %s\n", path)
	fmt.Printf("lang:       %s\n", res.Lang)
	fmt.Printf("encoding:   %s (mode=%s)\n", res.Encoding, res.Mode)
	fmt.Printf("raw:        %d bytes\n", res.RawSize)
	fmt.Printf("gzip(raw):  %d bytes\n", res.GzipRawSize)
	if res.ASTSize > 0 {
		fmt.Printf("protocol:   %d bytes (%.1f%% of gzip)\n", res.ASTSize, pct(res.ASTSize, res.GzipRawSize))
	}
	if res.RawDictSize > 0 {
		fmt.Printf("raw+dict:   %d bytes (%.1f%% of gzip)\n", res.RawDictSize, pct(res.RawDictSize, res.GzipRawSize))
	}
	if res.ASTDictSize > 0 {
		fmt.Printf("proto+dict: %d bytes (%.1f%% of gzip)\n", res.ASTDictSize, pct(res.ASTDictSize, res.GzipRawSize))
	}
	fmt.Printf("stored:     %d bytes (%.1f%% of raw, %.1f%% of gzip)\n",
		res.PayloadSize,
		pct(res.PayloadSize, res.RawSize),
		pct(res.PayloadSize, res.GzipRawSize))
	if res.NodeCount > 0 {
		fmt.Printf("leaves:     %d\n", res.NodeCount)
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
	enc := fs.String("encoding", codec.EncodingAST, "payload encoding")
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
	Path          string  `json:"path"`
	Lang          string  `json:"lang"`
	Encoding      string  `json:"encoding"`
	Mode          string  `json:"mode"`
	RawBytes      int     `json:"raw_bytes"`
	GzipBytes     int     `json:"gzip_bytes"`
	ProtoBytes    int     `json:"proto_bytes"` // protocol + flate
	RawDictBytes  int     `json:"raw_dict_bytes"`
	ASTDictBytes  int     `json:"ast_dict_bytes"`
	StoredBytes   int     `json:"stored_bytes"`
	ProtoVsGzip   float64 `json:"proto_vs_gzip_pct"`
	RawDictVsGzip float64 `json:"raw_dict_vs_gzip_pct"`
	StoredVsGzip  float64 `json:"stored_vs_gzip_pct"`
	EncodeMs      float64 `json:"encode_ms"`
	DecodeMs      float64 `json:"decode_ms"`
	GzipEncodeMs  float64 `json:"gzip_encode_ms"`
	GzipDecodeMs  float64 `json:"gzip_decode_ms"`
	SkippedReason string  `json:"skipped_reason,omitempty"`
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
	Files            int     `json:"files"`
	ASTStored        int     `json:"ast_stored"`
	DictStored       int     `json:"dict_stored"`
	GzipFallback     int     `json:"gzip_fallback"`
	TotalRaw         int64   `json:"total_raw_bytes"`
	TotalGzip        int64   `json:"total_gzip_bytes"`
	TotalProto       int64   `json:"total_proto_bytes"`
	TotalRawDict     int64   `json:"total_raw_dict_bytes"`
	TotalASTDict     int64   `json:"total_ast_dict_bytes"`
	TotalStored      int64   `json:"total_stored_bytes"`
	ProtoVsGzipPct   float64 `json:"proto_vs_gzip_pct"`
	RawDictVsGzipPct float64 `json:"raw_dict_vs_gzip_pct"`
	StoredVsGzipPct  float64 `json:"stored_vs_gzip_pct"`
	MedianProtoVsGzip float64 `json:"median_proto_vs_gzip_pct"`
	MeanEncodeMs     float64 `json:"mean_encode_ms"`
	MeanDecodeMs     float64 `json:"mean_decode_ms"`
	MeanGzipEncodeMs float64 `json:"mean_gzip_encode_ms"`
	MeanGzipDecodeMs float64 `json:"mean_gzip_decode_ms"`
	Verdict          string  `json:"verdict"`
}

func cmdBench(args []string) {
	fs := flag.NewFlagSet("bench", flag.ExitOnError)
	outPath := fs.String("out", "", "write JSON report")
	repeat := fs.Int("repeat", 3, "timing repeats")
	limit := fs.Int("limit", 0, "max files (0=all)")
	noAdapt := fs.Bool("no-adaptive", false, "force protocol storage")
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

	var protoRatios []float64
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
			NoAdaptive: *noAdapt,
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
			ProtoBytes:    last.ASTSize,
			RawDictBytes:  last.RawDictSize,
			ASTDictBytes:  last.ASTDictSize,
			StoredBytes:   last.PayloadSize,
			ProtoVsGzip:   pct(last.ASTSize, last.GzipRawSize),
			RawDictVsGzip: pct(last.RawDictSize, last.GzipRawSize),
			StoredVsGzip:  pct(last.PayloadSize, last.GzipRawSize),
			EncodeMs:      encMs / n,
			DecodeMs:      decMs / n,
			GzipEncodeMs:  gzEncMs / n,
			GzipDecodeMs:  gzDecMs / n,
			SkippedReason: last.SkippedReason,
		}
		report.Files = append(report.Files, fs)
		if last.ASTSize > 0 && last.GzipRawSize > 0 {
			protoRatios = append(protoRatios, fs.ProtoVsGzip)
		}
	}

	report.Summary = summarize(report.Files, protoRatios)
	printSummary(report)

	if *outPath != "" {
		b, err := json.MarshalIndent(report, "", "  ")
		must(err)
		must(os.WriteFile(*outPath, append(b, '\n'), 0o644))
		fmt.Printf("\nwrote %s\n", *outPath)
	}
}

func summarize(files []FileStat, protoRatios []float64) Summary {
	s := Summary{Files: len(files)}
	var enc, dec, gzEnc, gzDec float64
	for _, f := range files {
		s.TotalRaw += int64(f.RawBytes)
		s.TotalGzip += int64(f.GzipBytes)
		s.TotalProto += int64(f.ProtoBytes)
		s.TotalRawDict += int64(f.RawDictBytes)
		s.TotalASTDict += int64(f.ASTDictBytes)
		s.TotalStored += int64(f.StoredBytes)
		enc += f.EncodeMs
		dec += f.DecodeMs
		gzEnc += f.GzipEncodeMs
		gzDec += f.GzipDecodeMs
		switch f.Encoding {
		case codec.EncodingAST, codec.EncodingASTDict:
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
	s.ProtoVsGzipPct = pct64(s.TotalProto, s.TotalGzip)
	s.RawDictVsGzipPct = pct64(s.TotalRawDict, s.TotalGzip)
	s.StoredVsGzipPct = pct64(s.TotalStored, s.TotalGzip)
	if len(protoRatios) > 0 {
		sort.Float64s(protoRatios)
		s.MedianProtoVsGzip = protoRatios[len(protoRatios)/2]
	}
	switch {
	case s.StoredVsGzipPct < 95:
		s.Verdict = "adaptive protocol/dict store beats plain gzip on total bytes for this corpus"
	case s.StoredVsGzipPct <= 100.5:
		s.Verdict = "adaptive protocol/dict store is at or under plain gzip"
	default:
		s.Verdict = "adaptive store still larger than gzip (unexpected)"
	}
	if s.ProtoVsGzipPct > 0 && s.ProtoVsGzipPct < 105 {
		s.Verdict += "; protocol+flate is near parity with gzip alone"
	}
	if s.RawDictVsGzipPct > 0 && s.RawDictVsGzipPct < 100 {
		s.Verdict += fmt.Sprintf("; fixed lang dict alone is %.1f%% of gzip", s.RawDictVsGzipPct)
	}
	return s
}

func printSummary(r BenchReport) {
	s := r.Summary
	fmt.Printf("Source:           %s\n", r.Source)
	fmt.Printf("Files:            %d (%d protocol, %d dict, %d gzip)\n", s.Files, s.ASTStored, s.DictStored, s.GzipFallback)
	fmt.Printf("Total raw:        %d bytes\n", s.TotalRaw)
	fmt.Printf("Total gzip:       %d bytes (%.1f%% of raw)\n", s.TotalGzip, pct64(s.TotalGzip, s.TotalRaw))
	fmt.Printf("Total protocol:   %d bytes (%.1f%% of gzip)\n", s.TotalProto, s.ProtoVsGzipPct)
	if s.TotalRawDict > 0 {
		fmt.Printf("Total raw+dict:   %d bytes (%.1f%% of gzip)\n", s.TotalRawDict, s.RawDictVsGzipPct)
	}
	if s.TotalASTDict > 0 {
		fmt.Printf("Total proto+dict: %d bytes (%.1f%% of gzip)\n", s.TotalASTDict, pct64(s.TotalASTDict, s.TotalGzip))
	}
	fmt.Printf("Total stored:     %d bytes (%.1f%% of gzip) [adaptive min]\n", s.TotalStored, s.StoredVsGzipPct)
	fmt.Printf("Median proto/gzip:%.1f%%\n", s.MedianProtoVsGzip)
	fmt.Printf("Mean encode:      protocol %.2f ms  vs gzip %.2f ms\n", s.MeanEncodeMs, s.MeanGzipEncodeMs)
	fmt.Printf("Mean decode:      protocol %.2f ms  vs gzip %.2f ms\n", s.MeanDecodeMs, s.MeanGzipDecodeMs)
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

// RemoteBenchReport is written by `ast-remote bench-remote`.
type RemoteBenchReport struct {
	GeneratedAt    string  `json:"generated_at"`
	GoVersion      string  `json:"go_version"`
	Source         string  `json:"source"`
	SourceKind     string  `json:"source_kind"` // "git-repo" or "directory"
	Ref            string  `json:"ref"`
	Commits        int     `json:"commits"`
	Depth          int     `json:"depth,omitempty"`
	Repeats        int     `json:"repeats"`
	Objects        int     `json:"reachable_objects"`
	ProtoPushMs    float64 `json:"protocol_push_ms"`
	PlainPushMs    float64 `json:"plain_push_ms"`
	ProtoCloneMs   float64 `json:"protocol_clone_ms"`
	PlainCloneMs   float64 `json:"plain_clone_ms"`
	CloneRatio     float64 `json:"clone_ratio_protocol_over_plain"`
	AstStoreBytes  int64   `json:"ast_store_bytes"`
	PlainRemoteBytes int64 `json:"plain_remote_bytes"`
	ProtoGitBytes  int64   `json:"protocol_clone_git_bytes"`
	PlainGitBytes  int64   `json:"plain_clone_git_bytes"`
	ProtoWorkBytes int64   `json:"protocol_worktree_bytes"`
	PlainWorkBytes int64   `json:"plain_worktree_bytes"`
	FsckOK         bool    `json:"fsck_ok"`
	TreesMatch     bool    `json:"worktrees_match"`
	Verdict        string  `json:"verdict"`
}

func cmdBenchRemote(args []string) {
	fs := flag.NewFlagSet("bench-remote", flag.ExitOnError)
	outPath := fs.String("out", "", "write JSON report")
	repeat := fs.Int("repeat", 3, "clone repeats")
	commits := fs.Int("commits", 5, "synthetic history depth for non-git dirs")
	depth := fs.Int("depth", 0, "shallow depth for git repos (0=full)")
	refFlag := fs.String("ref", "", "ref/branch to publish (default HEAD)")
	helperPath := fs.String("helper", "./git-remote-ast", "path to git-remote-ast binary")
	portFlag := fs.Int("port", 0, "git-daemon port (0 = ephemeral)")
	skipFsck := fs.Bool("skip-fsck", false, "skip post-clone fsck")
	fs.Parse(args)
	if fs.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "bench-remote requires a source directory or git repo")
		os.Exit(2)
	}
	srcDir, err := filepath.Abs(fs.Arg(0))
	must(err)
	if *commits < 1 {
		*commits = 1
	}
	if *repeat < 1 {
		*repeat = 1
	}

	absHelper, err := filepath.Abs(*helperPath)
	must(err)
	if _, err := os.Stat(absHelper); err != nil {
		must(fmt.Errorf("build git-remote-ast first (%s): %w", absHelper, err))
	}
	daemonBin := gitDaemonPath()
	if daemonBin == "" {
		must(fmt.Errorf("git-daemon not found; needed for a fair local-server baseline"))
	}

	tmp, err := os.MkdirTemp("", "ast-remote-bench-*")
	must(err)
	defer os.RemoveAll(tmp)

	repo := filepath.Join(tmp, "repo")
	kind, ref, commitCount, err := prepareBenchRepo(srcDir, repo, *commits, *depth, *refFlag)
	must(err)

	objCount := countReachableObjects(repo)
	fmt.Fprintf(os.Stderr, "prepared %s (%s, ref=%s, %d commits, %d objects)\n",
		srcDir, kind, ref, commitCount, objCount)

	astStore := filepath.Join(tmp, "ast-store")
	remotesDir := filepath.Join(tmp, "remotes")
	plainRemote := filepath.Join(remotesDir, "plain.git")
	must(os.MkdirAll(remotesDir, 0o755))
	must(runCmd(tmp, nil, "git", "init", "--bare", "-b", ref, plainRemote))
	// Shallow source repos (e.g. kubernetes --depth=N) need this to publish to bare.
	must(runCmd(plainRemote, nil, "git", "config", "receive.shallowUpdate", "true"))

	helperDir := filepath.Dir(absHelper)
	pathEnv := append(os.Environ(), "PATH="+helperDir+string(os.PathListSeparator)+os.Getenv("PATH"))

	// One-time publish to both remotes (setup cost, reported separately).
	fmt.Fprintf(os.Stderr, "pushing to protocol store...\n")
	tPushProto := time.Now()
	must(runCmd(repo, pathEnv, "git", "push", "ast::"+astStore, ref+":"+ref))
	protoPush := time.Since(tPushProto)

	fmt.Fprintf(os.Stderr, "pushing to bare remote...\n")
	tPushPlain := time.Now()
	must(runCmd(repo, nil, "git", "push", plainRemote, ref+":"+ref))
	plainPush := time.Since(tPushPlain)

	port := *portFlag
	if port == 0 {
		port = freeTCPPort()
	}
	daemonLog := filepath.Join(tmp, "git-daemon.log")
	daemon, err := startGitDaemon(daemonBin, remotesDir, port, daemonLog)
	must(err)
	defer stopCmd(daemon)

	plainURL := fmt.Sprintf("git://127.0.0.1:%d/plain.git", port)
	// Warm the daemon with one untimed clone so listen/accept isn't in the sample.
	warm := filepath.Join(tmp, "warm-plain")
	must(runCmd(tmp, nil, "git", "clone", "--branch", ref, plainURL, warm))
	_ = os.RemoveAll(warm)

	var protoClone, plainClone time.Duration
	var lastProto, lastPlain string
	for i := 0; i < *repeat; i++ {
		fmt.Fprintf(os.Stderr, "clone round %d/%d...\n", i+1, *repeat)
		cloneProto := filepath.Join(tmp, fmt.Sprintf("clone-proto-%d", i))
		t0 := time.Now()
		must(runCmd(tmp, pathEnv, "git", "clone", "--branch", ref, "ast::"+astStore, cloneProto))
		protoClone += time.Since(t0)
		lastProto = cloneProto

		clonePlain := filepath.Join(tmp, fmt.Sprintf("clone-plain-%d", i))
		t1 := time.Now()
		must(runCmd(tmp, nil, "git", "clone", "--branch", ref, plainURL, clonePlain))
		plainClone += time.Since(t1)
		lastPlain = clonePlain

		// Drop earlier clones to keep disk use bounded on large repos.
		if i > 0 {
			_ = os.RemoveAll(filepath.Join(tmp, fmt.Sprintf("clone-proto-%d", i-1)))
			_ = os.RemoveAll(filepath.Join(tmp, fmt.Sprintf("clone-plain-%d", i-1)))
		}
	}

	n := float64(*repeat)
	protoMs := float64(protoClone.Microseconds()) / 1000.0 / n
	plainMs := float64(plainClone.Microseconds()) / 1000.0 / n

	fsckOK := true
	if !*skipFsck {
		fmt.Fprintf(os.Stderr, "fsck...\n")
		must(runCmd(lastProto, nil, "git", "fsck", "--full", "--no-progress"))
		must(runCmd(lastPlain, nil, "git", "fsck", "--full", "--no-progress"))
	} else {
		fsckOK = false
	}
	treesMatch := worktreesEqual(lastProto, lastPlain)
	if !treesMatch {
		detail := worktreeDiffSummary(lastProto, lastPlain)
		must(fmt.Errorf("cloned worktrees differ between protocol and plain remotes: %s", detail))
	}

	protoGit, protoWork := dirBytes(filepath.Join(lastProto, ".git")), worktreeBytes(lastProto)
	plainGit, plainWork := dirBytes(filepath.Join(lastPlain, ".git")), worktreeBytes(lastPlain)
	astBytes := dirBytes(astStore)
	plainBytes := dirBytes(plainRemote)

	report := RemoteBenchReport{
		GeneratedAt:      time.Now().UTC().Format(time.RFC3339),
		GoVersion:        runtime.Version(),
		Source:           srcDir,
		SourceKind:       kind,
		Ref:              ref,
		Commits:          commitCount,
		Depth:            *depth,
		Repeats:          *repeat,
		Objects:          objCount,
		ProtoPushMs:      float64(protoPush.Microseconds()) / 1000.0,
		PlainPushMs:      float64(plainPush.Microseconds()) / 1000.0,
		ProtoCloneMs:     protoMs,
		PlainCloneMs:     plainMs,
		CloneRatio:       protoMs / plainMs,
		AstStoreBytes:    astBytes,
		PlainRemoteBytes: plainBytes,
		ProtoGitBytes:    protoGit,
		PlainGitBytes:    plainGit,
		ProtoWorkBytes:   protoWork,
		PlainWorkBytes:   plainWork,
		FsckOK:           fsckOK || !*skipFsck,
		TreesMatch:       treesMatch,
	}
	if *skipFsck {
		report.FsckOK = false
	} else {
		report.FsckOK = true
	}
	switch {
	case report.CloneRatio < 0.9:
		report.Verdict = fmt.Sprintf("protocol full clone is faster than local git-daemon (%.2fx)", report.CloneRatio)
	case report.CloneRatio < 1.1:
		report.Verdict = "protocol full clone is within ~10% of a local git-daemon clone"
	case report.CloneRatio < 2:
		report.Verdict = "protocol full clone is slower than git-daemon but under 2×"
	default:
		report.Verdict = fmt.Sprintf("protocol full clone is %.1f× a local git-daemon clone (parse/rehydrate dominated)", report.CloneRatio)
	}

	fmt.Printf("Source tree:          %s (%s)\n", srcDir, kind)
	fmt.Printf("Ref:                  %s\n", ref)
	fmt.Printf("History:              %d commits, %d reachable objects\n", commitCount, objCount)
	fmt.Printf("Repeats:              %d full git clone(s)\n", *repeat)
	fmt.Printf("Baseline remote:      %s (git-daemon)\n", plainURL)
	fmt.Printf("Protocol remote:      ast::%s\n", astStore)
	fmt.Printf("Remote store size:    protocol %d B  vs bare %d B (%.1f%%)\n",
		astBytes, plainBytes, pct64(astBytes, plainBytes))
	fmt.Printf("Setup push protocol:  %.1f ms\n", report.ProtoPushMs)
	fmt.Printf("Setup push plain:     %.1f ms\n", report.PlainPushMs)
	fmt.Printf("Mean clone protocol:  %.1f ms  (.git %d B, worktree %d B)\n",
		report.ProtoCloneMs, report.ProtoGitBytes, report.ProtoWorkBytes)
	fmt.Printf("Mean clone plain:     %.1f ms  (.git %d B, worktree %d B)\n",
		report.PlainCloneMs, report.PlainGitBytes, report.PlainWorkBytes)
	fmt.Printf("Clone ratio:          protocol/plain = %.2fx\n", report.CloneRatio)
	if *skipFsck {
		fmt.Printf("Post-clone fsck:      skipped\n")
	} else {
		fmt.Printf("Post-clone fsck:      ok (both)\n")
	}
	fmt.Printf("Worktrees match:      %v\n", treesMatch)
	fmt.Printf("Verdict:              %s\n", report.Verdict)

	if *outPath != "" {
		b, err := json.MarshalIndent(report, "", "  ")
		must(err)
		must(os.WriteFile(*outPath, append(b, '\n'), 0o644))
		fmt.Printf("\nwrote %s\n", *outPath)
	}
}

// prepareBenchRepo materializes a local repo under dst for publishing.
// If src is a git checkout, it is cloned (optionally shallow). Otherwise a
// synthetic multi-commit history is built from the directory tree.
func prepareBenchRepo(src, dst string, syntheticCommits, depth int, refFlag string) (kind, ref string, commitCount int, err error) {
	if isGitRepo(src) {
		kind = "git-repo"
		args := []string{"clone", "--no-local"}
		if depth > 0 {
			args = append(args, fmt.Sprintf("--depth=%d", depth))
		}
		if refFlag != "" {
			args = append(args, "--branch", refFlag)
		}
		args = append(args, src, dst)
		if err := runCmd("", nil, "git", args...); err != nil {
			return "", "", 0, err
		}
		_ = runCmd(dst, nil, "git", "config", "commit.gpgsign", "false")
		ref, err = resolveRef(dst, refFlag)
		if err != nil {
			return "", "", 0, err
		}
		// Ensure the published ref name exists locally as a branch tip.
		if err := runCmd(dst, nil, "git", "checkout", "-B", ref, "HEAD"); err != nil {
			return "", "", 0, err
		}
		commitCount = countCommits(dst, ref)
		return kind, ref, commitCount, nil
	}

	kind = "directory"
	if err := runCmd("", nil, "git", "init", "-b", "main", dst); err != nil {
		return "", "", 0, err
	}
	if err := runCmd(dst, nil, "git", "config", "user.email", "bench@example.com"); err != nil {
		return "", "", 0, err
	}
	if err := runCmd(dst, nil, "git", "config", "user.name", "Bench"); err != nil {
		return "", "", 0, err
	}
	if err := runCmd(dst, nil, "git", "config", "commit.gpgsign", "false"); err != nil {
		return "", "", 0, err
	}
	if err := seedSyntheticHistory(src, dst, syntheticCommits); err != nil {
		return "", "", 0, err
	}
	return kind, "main", syntheticCommits, nil
}

func isGitRepo(path string) bool {
	// Only treat path as a repo if it *is* the work tree / bare root, not merely
	// nested inside some parent checkout (e.g. testdata/ under this playground).
	if st, err := os.Stat(filepath.Join(path, ".git")); err == nil && (st.IsDir() || st.Mode().IsRegular()) {
		return true
	}
	if st, err := os.Stat(filepath.Join(path, "HEAD")); err == nil && !st.IsDir() {
		if _, err := os.Stat(filepath.Join(path, "objects")); err == nil {
			return true
		}
	}
	out, err := exec.Command("git", "-C", path, "rev-parse", "--show-toplevel").Output()
	if err != nil {
		out, err = exec.Command("git", "-C", path, "rev-parse", "--git-dir").Output()
		if err != nil {
			return false
		}
		// bare: git-dir should equal path
		gd := strings.TrimSpace(string(out))
		if !filepath.IsAbs(gd) {
			gd = filepath.Join(path, gd)
		}
		absPath, _ := filepath.Abs(path)
		absGD, _ := filepath.Abs(gd)
		return absPath == absGD
	}
	top := strings.TrimSpace(string(out))
	absPath, _ := filepath.Abs(path)
	absTop, _ := filepath.Abs(top)
	return absPath == absTop
}

func resolveRef(repo, refFlag string) (string, error) {
	if refFlag != "" {
		return refFlag, nil
	}
	out, err := exec.Command("git", "-C", repo, "symbolic-ref", "--short", "HEAD").Output()
	if err == nil {
		return strings.TrimSpace(string(out)), nil
	}
	// Detached HEAD: invent a branch name from the tip.
	return "bench", nil
}

func countCommits(repo, ref string) int {
	out, err := exec.Command("git", "-C", repo, "rev-list", "--count", ref).Output()
	if err != nil {
		return 0
	}
	var n int
	_, _ = fmt.Sscanf(strings.TrimSpace(string(out)), "%d", &n)
	return n
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

func gitDaemonPath() string {
	if p, err := exec.LookPath("git-daemon"); err == nil {
		return p
	}
	candidates := []string{
		"/usr/lib/git-core/git-daemon",
		"/usr/libexec/git-core/git-daemon",
	}
	for _, c := range candidates {
		if st, err := os.Stat(c); err == nil && !st.IsDir() {
			return c
		}
	}
	return ""
}

func freeTCPPort() int {
	// Ask the kernel for an ephemeral port, then release it for git-daemon.
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	must(err)
	defer ln.Close()
	return ln.Addr().(*net.TCPAddr).Port
}

func startGitDaemon(bin, basePath string, port int, logPath string) (*exec.Cmd, error) {
	logF, err := os.Create(logPath)
	if err != nil {
		return nil, err
	}
	cmd := exec.Command(bin,
		"--reuseaddr",
		"--listen=127.0.0.1",
		fmt.Sprintf("--port=%d", port),
		"--base-path="+basePath,
		"--export-all",
		basePath,
	)
	cmd.Stdout = logF
	cmd.Stderr = logF
	if err := cmd.Start(); err != nil {
		logF.Close()
		return nil, err
	}
	// Wait until the port accepts connections.
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		c, err := net.DialTimeout("tcp", fmt.Sprintf("127.0.0.1:%d", port), 100*time.Millisecond)
		if err == nil {
			c.Close()
			return cmd, nil
		}
		time.Sleep(25 * time.Millisecond)
	}
	stopCmd(cmd)
	return nil, fmt.Errorf("git-daemon did not become ready on port %d (see %s)", port, logPath)
}

func stopCmd(cmd *exec.Cmd) {
	if cmd == nil || cmd.Process == nil {
		return
	}
	_ = cmd.Process.Kill()
	_, _ = cmd.Process.Wait()
}

// seedSyntheticHistory copies the source tree and creates N commits so clone
// must walk a real object graph (parents, trees, blobs), not a single tip.
func seedSyntheticHistory(srcDir, repo string, n int) error {
	if err := copyTree(srcDir, filepath.Join(repo, "src")); err != nil {
		return err
	}
	for i := 1; i <= n; i++ {
		marker := filepath.Join(repo, "src", fmt.Sprintf("commit_%02d.txt", i))
		if err := os.WriteFile(marker, []byte(fmt.Sprintf("commit %d\n", i)), 0o644); err != nil {
			return err
		}
		// Touch a source file each commit so trees/blobs change.
		touch := filepath.Join(repo, "src", "bench_note.go")
		body := fmt.Sprintf("package src\n\n// bench commit %d\nconst BenchN = %d\n", i, i)
		if err := os.WriteFile(touch, []byte(body), 0o644); err != nil {
			return err
		}
		date := fmt.Sprintf("2020-01-%02dT12:00:00", i)
		env := append(os.Environ(),
			"GIT_AUTHOR_DATE="+date,
			"GIT_COMMITTER_DATE="+date,
		)
		if err := runCmd(repo, nil, "git", "add", "-A"); err != nil {
			return err
		}
		if err := runCmd(repo, env, "git", "commit", "-m", fmt.Sprintf("bench commit %d", i)); err != nil {
			return err
		}
	}
	return nil
}

func copyTree(src, dst string) error {
	return filepath.WalkDir(src, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(src, path)
		if err != nil {
			return err
		}
		if rel == "." {
			return os.MkdirAll(dst, 0o755)
		}
		out := filepath.Join(dst, rel)
		if d.IsDir() {
			if d.Name() == ".git" {
				return filepath.SkipDir
			}
			return os.MkdirAll(out, 0o755)
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		if err := os.MkdirAll(filepath.Dir(out), 0o755); err != nil {
			return err
		}
		return os.WriteFile(out, data, 0o644)
	})
}

func countReachableObjects(repo string) int {
	out, err := exec.Command("git", "-C", repo, "rev-list", "--objects", "--all").Output()
	must(err)
	n := 0
	for _, line := range strings.Split(string(out), "\n") {
		if strings.TrimSpace(line) != "" {
			n++
		}
	}
	return n
}

func worktreesEqual(a, b string) bool {
	return worktreeDiffSummary(a, b) == ""
}

func worktreeDiffSummary(a, b string) string {
	type file struct {
		rel  string
		data []byte
		mode os.FileMode
	}
	collect := func(root string) ([]file, error) {
		var files []file
		err := filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
			if err != nil {
				return err
			}
			rel, err := filepath.Rel(root, path)
			if err != nil {
				return err
			}
			if d.IsDir() {
				if d.Name() == ".git" {
					return filepath.SkipDir
				}
				return nil
			}
			info, err := d.Info()
			if err != nil {
				return err
			}
			if info.Mode()&os.ModeSymlink != 0 {
				target, err := os.Readlink(path)
				if err != nil {
					return err
				}
				files = append(files, file{rel: rel, data: []byte("symlink->" + target), mode: info.Mode()})
				return nil
			}
			data, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			files = append(files, file{rel: rel, data: data, mode: info.Mode()})
			return nil
		})
		sort.Slice(files, func(i, j int) bool { return files[i].rel < files[j].rel })
		return files, err
	}
	fa, err := collect(a)
	if err != nil {
		return "collect a: " + err.Error()
	}
	fb, err := collect(b)
	if err != nil {
		return "collect b: " + err.Error()
	}
	if len(fa) != len(fb) {
		return fmt.Sprintf("file count %d vs %d", len(fa), len(fb))
	}
	for i := range fa {
		if fa[i].rel != fb[i].rel {
			return fmt.Sprintf("path %q vs %q", fa[i].rel, fb[i].rel)
		}
		if fa[i].mode != fb[i].mode {
			return fmt.Sprintf("%s mode %v vs %v", fa[i].rel, fa[i].mode, fb[i].mode)
		}
		if string(fa[i].data) != string(fb[i].data) {
			return fmt.Sprintf("%s content (%d vs %d bytes)", fa[i].rel, len(fa[i].data), len(fb[i].data))
		}
	}
	return ""
}

func dirBytes(root string) int64 {
	var n int64
	_ = filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
		if err != nil || d.IsDir() {
			return err
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		n += info.Size()
		return nil
	})
	return n
}

func worktreeBytes(root string) int64 {
	var n int64
	_ = filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if d.Name() == ".git" {
				return filepath.SkipDir
			}
			return nil
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		n += info.Size()
		return nil
	})
	return n
}

var _ = io.Discard
