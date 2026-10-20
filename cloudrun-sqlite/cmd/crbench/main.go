// Command crbench measures cloudrun-sqlite under a Cloud Run simulator.
//
//	crbench coldstart -app ./cloudrun-sqlite -replica-url s3://bench/cold -rows 10000,100000,1000000
//	crbench soak -app ./cloudrun-sqlite -replica-url s3://bench/soak -duration 2m
//	crbench live -url https://service.run.app -duration 1m -roll -project PROJECT
package main

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"math/rand/v2"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"time"

	"github.com/benbjohnson/litestream"
	_ "github.com/benbjohnson/litestream/file"
	_ "github.com/benbjohnson/litestream/gs"
	_ "github.com/benbjohnson/litestream/s3"
	// With the vfs tag, Litestream's VFS calls SQLite's C API, which
	// go-sqlite3 links.
	_ "github.com/mattn/go-sqlite3"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/crsim"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/scenario"
)

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: crbench coldstart|soak|live [flags]")
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "coldstart":
		err = coldstart(os.Args[2:])
	case "soak":
		err = soak(os.Args[2:])
	case "live":
		err = live(os.Args[2:])
	default:
		err = fmt.Errorf("unknown command %q", os.Args[1])
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

type envFlag []string

func (e *envFlag) String() string     { return strings.Join(*e, ",") }
func (e *envFlag) Set(v string) error { *e = append(*e, v); return nil }

type common struct {
	app        string
	replicaURL string
	env        envFlag
	throttle   bool
	logs       string
	adminToken string
}

func (c *common) register(fs *flag.FlagSet) {
	fs.StringVar(&c.app, "app", "./cloudrun-sqlite", "path to the cloudrun-sqlite binary")
	fs.StringVar(&c.replicaURL, "replica-url", "", "replica URL; coldstart appends /rows-N")
	fs.Var(&c.env, "env", "KEY=VALUE for instances (repeatable)")
	fs.BoolVar(&c.throttle, "throttle", false, "freeze instances between requests")
	fs.StringVar(&c.logs, "logs", "", "file for instance logs (default discard)")
}

func (c *common) sim(replicaURL string) (*crsim.Sim, *httptest.Server, func(), error) {
	out := io.Discard
	var closeLog func() error
	if c.logs != "" {
		f, err := os.OpenFile(c.logs, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0o644)
		if err != nil {
			return nil, nil, nil, err
		}
		out, closeLog = f, f.Close
	}
	if c.adminToken == "" {
		c.adminToken = strconv.FormatUint(rand.Uint64(), 36)
	}
	sim := crsim.New(crsim.Config{
		Command:  []string{c.app},
		Env:      append([]string{"REPLICA_URL=" + replicaURL, "ADMIN_TOKEN=" + c.adminToken}, c.env...),
		Throttle: c.throttle,
		Output:   out,
		Logger:   slog.New(slog.NewTextHandler(out, nil)).With("component", "crsim"),
	})
	srv := httptest.NewServer(sim)
	return sim, srv, func() {
		srv.Close()
		sim.Close()
		if closeLog != nil {
			closeLog()
		}
	}, nil
}

func soak(args []string) error {
	var c common
	cfg := scenario.SoakConfig{}
	fs := flag.NewFlagSet("soak", flag.ExitOnError)
	c.register(fs)
	fs.DurationVar(&cfg.Duration, "duration", time.Minute, "how long to run")
	fs.IntVar(&cfg.Writers, "writers", 8, "concurrent writers")
	fs.IntVar(&cfg.Readers, "readers", 8, "concurrent readers")
	fs.IntVar(&cfg.BodySize, "body-size", 200, "bytes per item")
	fs.DurationVar(&cfg.WriteInterval, "write-interval", 0, "pause between each writer's writes (0 writes as fast as possible)")
	fs.DurationVar(&cfg.CrashEvery, "crash-every", 20*time.Second, "SIGKILL the instance this often (0 disables)")
	fs.DurationVar(&cfg.ScaleEvery, "scale-every", 15*time.Second, "scale to zero this often (0 disables)")
	fs.DurationVar(&cfg.DeployEvery, "deploy-every", 25*time.Second, "deploy a new revision this often (0 disables)")
	fs.DurationVar(&cfg.Overlap, "overlap", 3*time.Second, "how long both revisions serve during a deploy")
	jsonOut := fs.String("json", "", "write the result as JSON to this file")
	fs.Parse(args)

	sim, srv, done, err := c.sim(c.replicaURL)
	if err != nil {
		return err
	}
	defer done()
	cfg.URL = srv.URL
	cfg.Sim = sim
	cfg.AdminToken = c.adminToken
	cfg.Logf = func(format string, args ...any) {
		fmt.Fprintf(os.Stderr, "%s "+format+"\n", append([]any{time.Now().Format("15:04:05.000")}, args...)...)
	}
	res, err := scenario.Soak(context.Background(), cfg)
	if err != nil {
		return err
	}
	if *jsonOut != "" {
		b, _ := json.MarshalIndent(res, "", "  ")
		if err := os.WriteFile(*jsonOut, b, 0o644); err != nil {
			return err
		}
	}
	printSoak(res)
	if len(res.Violations) > 0 {
		return fmt.Errorf("%d violations", len(res.Violations))
	}
	return nil
}

func printSoak(r *scenario.SoakResult) {
	if r.Integrity == "skipped" {
		fmt.Printf("acknowledged writes: %d\n", r.Acked)
	} else {
		fmt.Printf("acknowledged writes: %d (items in database: %d)\n", r.Acked, r.Items)
	}
	fmt.Printf("write latency ms: p50 %.1f  p90 %.1f  p99 %.1f  max %.1f\n", r.WriteLatency.P50, r.WriteLatency.P90, r.WriteLatency.P99, r.WriteLatency.Max)
	fmt.Printf("read latency ms:  p50 %.1f  p90 %.1f  p99 %.1f  max %.1f  (%d reads)\n", r.ReadLatency.P50, r.ReadLatency.P90, r.ReadLatency.P99, r.ReadLatency.Max, r.ReadLatency.Count)
	keys := make([]string, 0, len(r.Statuses))
	for k := range r.Statuses {
		keys = append(keys, k)
	}
	slices.Sort(keys)
	for _, k := range keys {
		fmt.Printf("  %-12s %d\n", k, r.Statuses[k])
	}
	fmt.Printf("chaos: %d crashes, %d scale-to-zeros, %d deploys; %d instances\n", r.Crashes, r.ScaleToZeros, r.Deploys, len(r.Instances))
	if len(r.Instances) == 0 {
		fmt.Printf("stale reads during overlap: %d\n", r.StaleReads)
		fmt.Printf("after restart: %d missing, %d mismatched; integrity_check: %s\n", r.Missing, r.Mismatched, r.Integrity)
		fmt.Printf("violations: %d\n", len(r.Violations))
		for i, v := range r.Violations {
			if i == 10 {
				fmt.Printf("  ... %d more\n", len(r.Violations)-10)
				break
			}
			fmt.Println("  " + v)
		}
		return
	}
	var exits = map[string]int{}
	var peakRSS, peakDisk int64
	var ready []float64
	for _, in := range r.Instances {
		exits[in.Exit]++
		peakRSS = max(peakRSS, in.PeakRSS)
		peakDisk = max(peakDisk, in.PeakDisk)
		ready = append(ready, in.ReadyMillis)
	}
	slices.Sort(ready)
	fmt.Printf("instance exits: %v; peak RSS %.0f MiB, peak scratch %.1f MiB\n", exits, float64(peakRSS)/(1<<20), float64(peakDisk)/(1<<20))
	if len(ready) > 0 {
		fmt.Printf("instance start-to-listen ms: median %.0f, max %.0f\n", ready[len(ready)/2], ready[len(ready)-1])
	}
	fmt.Printf("stale reads during overlap: %d\n", r.StaleReads)
	fmt.Printf("after restart: %d missing, %d mismatched; integrity_check: %s\n", r.Missing, r.Mismatched, r.Integrity)
	fmt.Printf("violations: %d\n", len(r.Violations))
	for i, v := range r.Violations {
		if i == 10 {
			fmt.Printf("  ... %d more\n", len(r.Violations)-10)
			break
		}
		fmt.Println("  " + v)
	}
}

// live runs the soak workload against a service that is already up, then
// reads every acknowledged write back. -roll starts a new Cloud Run
// revision first so the read-back comes from the replica.
func live(args []string) error {
	cfg := scenario.SoakConfig{}
	fs := flag.NewFlagSet("live", flag.ExitOnError)
	url := fs.String("url", "", "base URL of the running service")
	fs.DurationVar(&cfg.Duration, "duration", time.Minute, "how long to run")
	fs.IntVar(&cfg.Writers, "writers", 8, "concurrent writers")
	fs.IntVar(&cfg.Readers, "readers", 8, "concurrent readers")
	fs.IntVar(&cfg.BodySize, "body-size", 200, "bytes per item")
	fs.DurationVar(&cfg.WriteInterval, "write-interval", 0, "pause between each writer's writes (0 writes as fast as possible)")
	admin := fs.String("admin-token", "", "bearer token for GET /admin/check (optional)")
	roll := fs.Bool("roll", false, "deploy a new Cloud Run revision before reading writes back")
	project := fs.String("project", "", "Google Cloud project, required with -roll")
	region := fs.String("region", "us-central1", "Cloud Run region")
	service := fs.String("service", "cloudrun-sqlite", "Cloud Run service name")
	jsonOut := fs.String("json", "", "write the result as JSON to this file")
	fs.Parse(args)
	if *url == "" {
		return errors.New("-url is required")
	}
	if *roll && *project == "" {
		return errors.New("-roll requires -project")
	}
	*url = strings.TrimRight(*url, "/")
	cfg.URL = *url
	cfg.AdminToken = *admin
	cfg.Logf = func(format string, args ...any) {
		fmt.Fprintf(os.Stderr, "%s "+format+"\n", append([]any{time.Now().Format("15:04:05.000")}, args...)...)
	}

	var during remoteStats
	var haveDuring bool
	var cold *liveCold
	cfg.BeforeVerify = func(ctx context.Context) error {
		client := &http.Client{Timeout: 30 * time.Second}
		if err := getJSON(client, *url+"/stats", &during); err != nil {
			fmt.Fprintf(os.Stderr, "stats before read-back: %v\n", err)
		} else {
			haveDuring = true
		}
		if !*roll {
			return nil
		}
		c, err := rollService(ctx, *project, *region, *service, *url, during.Instance)
		if err != nil {
			return err
		}
		cold = c
		return nil
	}

	res, err := scenario.Soak(context.Background(), cfg)
	if res != nil {
		printSoak(res)
	}
	if haveDuring {
		fmt.Println("server during load:")
		printRemoteStats(&during)
	}
	if cold != nil {
		fmt.Printf("new instance %s: request %.0f ms, database open %.0f ms\n", cold.Instance, cold.RequestMS, cold.OpenMS)
	}
	if *jsonOut != "" && res != nil {
		b, _ := json.MarshalIndent(map[string]any{"soak": res, "during": during, "cold": cold}, "", "  ")
		if werr := os.WriteFile(*jsonOut, b, 0o644); werr != nil {
			return werr
		}
	}
	if err != nil {
		return err
	}
	if len(res.Violations) > 0 {
		return fmt.Errorf("%d violations", len(res.Violations))
	}
	return nil
}

type liveCold struct {
	Instance  string  `json:"instance"`
	RequestMS float64 `json:"request_ms"`
	OpenMS    float64 `json:"open_ms"`
}

type remoteStats struct {
	Instance string  `json:"instance"`
	UptimeMS float64 `json:"uptime_ms"`
	Store    struct {
		OpenMS     float64 `json:"open_ms"`
		Writes     int64   `json:"writes"`
		Batches    int64   `json:"batches"`
		Conflicts  int64   `json:"conflicts"`
		ReadWait   pct     `json:"read_wait"`
		ReadQuery  pct     `json:"read_query"`
		WriteQueue pct     `json:"write_queue"`
		Tx         pct     `json:"tx"`
		Flush      pct     `json:"flush"`
		GCS        struct {
			Get  pct `json:"get"`
			List pct `json:"list"`
			Put  pct `json:"put"`
		} `json:"gcs"`
	} `json:"store"`
}

type pct struct {
	Count int     `json:"count"`
	P50   float64 `json:"p50_ms"`
	P90   float64 `json:"p90_ms"`
	P99   float64 `json:"p99_ms"`
	Max   float64 `json:"max_ms"`
}

func printRemoteStats(st *remoteStats) {
	s := st.Store
	fmt.Printf("  instance %s, open %.1f ms, writes %d, batches %d, conflicts %d\n", st.Instance, s.OpenMS, s.Writes, s.Batches, s.Conflicts)
	printPct("read wait", s.ReadWait)
	printPct("read query", s.ReadQuery)
	printPct("write queue", s.WriteQueue)
	printPct("sqlite tx", s.Tx)
	printPct("flush", s.Flush)
	printPct("replica get", s.GCS.Get)
	printPct("replica list", s.GCS.List)
	printPct("replica put", s.GCS.Put)
}

func printPct(name string, p pct) {
	fmt.Printf("  %-12s n=%-6d p50 %6.1f  p90 %6.1f  p99 %6.1f  max %6.1f ms\n", name, p.Count, p.P50, p.P90, p.P99, p.Max)
}

// rollService deploys a new revision and waits until /stats reports a
// different instance. The successful request's time is how long that
// request took, which includes a cold start when Cloud Run has not
// already started the container.
func rollService(ctx context.Context, project, region, service, url, oldInstance string) (*liveCold, error) {
	ctx, cancel := context.WithTimeout(ctx, 4*time.Minute)
	defer cancel()
	epoch := strconv.FormatInt(time.Now().Unix(), 10)
	cmd := exec.CommandContext(ctx, "gcloud", "run", "services", "update", service,
		"--project", project,
		"--region", region,
		"--update-env-vars", "LIVE_EPOCH="+epoch,
		"--quiet",
	)
	cmd.Stdout, cmd.Stderr = os.Stderr, os.Stderr
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("roll revision: %w", err)
	}
	client := &http.Client{Timeout: 2 * time.Minute}
	deadline := time.Now().Add(2 * time.Minute)
	var last error
	for time.Now().Before(deadline) {
		start := time.Now()
		var st remoteStats
		err := getJSON(client, url+"/stats", &st)
		if err == nil && st.Instance != "" && st.Instance != oldInstance {
			return &liveCold{Instance: st.Instance, RequestMS: ms(time.Since(start)), OpenMS: st.Store.OpenMS}, nil
		}
		if err != nil {
			last = err
		} else {
			last = fmt.Errorf("still instance %s", st.Instance)
		}
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		case <-time.After(300 * time.Millisecond):
		}
	}
	return nil, fmt.Errorf("new instance did not serve: %w", last)
}

type coldResult struct {
	Rows         int     `json:"rows"`
	DBBytes      int64   `json:"db_bytes"`
	ListenMillis float64 `json:"start_to_listen_ms"`
	FirstMillis  float64 `json:"first_request_ms"`
	OpenMillis   float64 `json:"open_ms"`
	WarmP50      float64 `json:"random_read_p50_ms"`
	WarmP99      float64 `json:"random_read_p99_ms"`
	RestoreMs    float64 `json:"full_restore_ms"`
}

func coldstart(args []string) error {
	var c common
	fs := flag.NewFlagSet("coldstart", flag.ExitOnError)
	c.register(fs)
	rowsFlag := fs.String("rows", "10000,100000,1000000", "comma-separated row counts to seed (1000 bytes each)")
	trials := fs.Int("trials", 5, "cold starts per size")
	reads := fs.Int("reads", 200, "random reads after each cold start")
	skipSeed := fs.Bool("skip-seed", false, "reuse previously seeded replicas")
	jsonOut := fs.String("json", "", "write results as JSON to this file")
	fs.Parse(args)

	var results []coldResult
	for _, s := range strings.Split(*rowsFlag, ",") {
		rows, err := strconv.Atoi(strings.TrimSpace(s))
		if err != nil {
			return err
		}
		url := withPath(c.replicaURL, "rows-"+strconv.Itoa(rows))
		if !*skipSeed {
			cmd := exec.Command(c.app, "seed", "-replica-url", url, "-rows", strconv.Itoa(rows), "-row-size", "1000", "-force")
			cmd.Env = append(os.Environ(), c.env...)
			cmd.Stdout, cmd.Stderr = os.Stderr, os.Stderr
			if err := cmd.Run(); err != nil {
				return fmt.Errorf("seed %d rows: %w", rows, err)
			}
		}
		r, err := measureSize(&c, url, rows, *trials, *reads)
		if err != nil {
			return err
		}
		results = append(results, r)
		fmt.Fprintf(os.Stderr, "%+v\n", r)
	}

	fmt.Println("| rows | database | start to listen | first request | random read p50 / p99 | full restore (old approach) |")
	fmt.Println("|---:|---:|---:|---:|---:|---:|")
	for _, r := range results {
		fmt.Printf("| %d | %.0f MiB | %.0f ms | %.0f ms | %.1f / %.1f ms | %.0f ms |\n",
			r.Rows, float64(r.DBBytes)/(1<<20), r.ListenMillis, r.FirstMillis, r.WarmP50, r.WarmP99, r.RestoreMs)
	}
	if *jsonOut != "" {
		b, _ := json.MarshalIndent(results, "", "  ")
		return os.WriteFile(*jsonOut, b, 0o644)
	}
	return nil
}

func measureSize(c *common, url string, rows, trials, reads int) (coldResult, error) {
	res := coldResult{Rows: rows}
	sim, srv, done, err := c.sim(url)
	if err != nil {
		return res, err
	}
	defer done()
	client := &http.Client{Timeout: 5 * time.Minute}

	var listen, first, open, warm []float64
	for range trials {
		sim.ScaleToZero()
		start := time.Now()
		if err := getJSON(client, srv.URL+"/items/"+strconv.Itoa(1+rand.IntN(rows)), nil); err != nil {
			return res, err
		}
		first = append(first, ms(time.Since(start)))
		insts := sim.Instances()
		listen = append(listen, insts[len(insts)-1].ReadyMillis)

		var st struct {
			Store struct {
				OpenMillis float64 `json:"open_ms"`
			}
		}
		if err := getJSON(client, srv.URL+"/stats", &st); err != nil {
			return res, err
		}
		open = append(open, st.Store.OpenMillis)

		for range reads {
			start := time.Now()
			if err := getJSON(client, srv.URL+"/items/"+strconv.Itoa(1+rand.IntN(rows)), nil); err != nil {
				return res, err
			}
			warm = append(warm, ms(time.Since(start)))
		}
	}
	res.ListenMillis = median(listen)
	res.FirstMillis = median(first)
	res.OpenMillis = median(open)
	slices.Sort(warm)
	res.WarmP50 = warm[len(warm)/2]
	res.WarmP99 = warm[len(warm)*99/100]

	// Restore the whole database to a local file, which is what the earlier
	// sidecar version did on every cold start.
	dir, err := os.MkdirTemp("", "restore-*")
	if err != nil {
		return res, err
	}
	defer os.RemoveAll(dir)
	client2, err := litestream.NewReplicaClientFromURL(url)
	if err != nil {
		return res, err
	}
	if err := client2.Init(context.Background()); err != nil {
		return res, err
	}
	out := filepath.Join(dir, "db")
	start := time.Now()
	if err := litestream.NewReplicaWithClient(nil, client2).Restore(context.Background(), litestream.RestoreOptions{OutputPath: out}); err != nil {
		return res, fmt.Errorf("restore: %w", err)
	}
	res.RestoreMs = ms(time.Since(start))
	if fi, err := os.Stat(out); err == nil {
		res.DBBytes = fi.Size()
	}
	return res, nil
}

func getJSON(client *http.Client, url string, into any) error {
	resp, err := client.Get(url)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		return err
	}
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("GET %s: %d %s", url, resp.StatusCode, b)
	}
	if into != nil {
		return json.Unmarshal(b, into)
	}
	return nil
}

// withPath appends a path element to a replica URL, keeping its query.
func withPath(u, elem string) string {
	base, query, _ := strings.Cut(u, "?")
	base = strings.TrimSuffix(base, "/") + "/" + elem
	if query != "" {
		return base + "?" + query
	}
	return base
}

func median(xs []float64) float64 {
	xs = slices.Clone(xs)
	slices.Sort(xs)
	return xs[len(xs)/2]
}

func ms(d time.Duration) float64 { return float64(d.Microseconds()) / 1000 }
