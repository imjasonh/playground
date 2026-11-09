// Command crbench measures cloudrun-duckdb under a Cloud Run simulator.
//
//	crbench coldstart -app ./cloudrun-duckdb -replica-url 'gs://bench/cold?endpoint=http://127.0.0.1:9100' -rows 10000,100000
//	crbench soak -app ./cloudrun-duckdb -replica-url 'gs://bench/soak?endpoint=http://127.0.0.1:9100' -duration 1m
//	crbench live -url https://service.run.app -duration 1m -roll -project PROJECT
//
// When the replica URL names a fakegcs endpoint, coldstart and soak also
// report how many object-storage requests the run made.
package main

import (
	"context"
	"encoding/json/jsontext"
	"encoding/json/v2"
	"errors"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"math/rand/v2"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"slices"
	"strconv"
	"strings"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/crsim"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/fakegcs"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/scenario"
)

func main() {
	if len(os.Args) < 2 {
		slog.Error("usage: crbench coldstart|soak|live [flags]")
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
		clog.Fatal("crbench", "err", err)
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
	fs.StringVar(&c.app, "app", "./cloudrun-duckdb", "path to the cloudrun-duckdb binary")
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
	sim := crsim.New(clog.WithLogger(context.Background(), clog.NewLogger(
		slog.New(slog.NewTextHandler(out, nil)).With("component", "crsim"),
	)), crsim.Config{
		Command:  []string{c.app},
		Env:      append([]string{"REPLICA_URL=" + replicaURL, "ADMIN_TOKEN=" + c.adminToken}, c.env...),
		Throttle: c.throttle,
		Output:   out,
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

// fakeCounts reads request counts from the fakegcs server that a replica
// URL's endpoint names. It returns false for any other replica.
func fakeCounts(replicaURL string) (fakegcs.Counts, bool) {
	u, err := url.Parse(replicaURL)
	if err != nil || u.Scheme != "gs" || u.Query().Get("endpoint") == "" {
		return fakegcs.Counts{}, false
	}
	var c fakegcs.Counts
	if err := getJSON(&http.Client{Timeout: 5 * time.Second}, strings.TrimRight(u.Query().Get("endpoint"), "/")+"/_fakegcs/stats", &c); err != nil {
		return fakegcs.Counts{}, false
	}
	return c, true
}

func diffCounts(a, b fakegcs.Counts) fakegcs.Counts {
	return fakegcs.Counts{Get: b.Get - a.Get, List: b.List - a.List, Create: b.Create - a.Create, Delete: b.Delete - a.Delete, BytesIn: b.BytesIn - a.BytesIn, BytesOut: b.BytesOut - a.BytesOut}
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
	before, counted := fakeCounts(c.replicaURL)
	var during fakegcs.Counts
	cfg.BeforeVerify = func(context.Context) error {
		if counted {
			after, _ := fakeCounts(c.replicaURL)
			during = diffCounts(before, after)
		}
		return nil
	}
	// The soak scales to zero before reading writes back, so read the
	// loaded instance's /stats just before the load ends.
	var server remoteStats
	statsDone := make(chan bool, 1)
	go func() {
		time.Sleep(cfg.Duration - cfg.Duration/20)
		statsDone <- getJSON(&http.Client{Timeout: 30 * time.Second}, srv.URL+"/stats", &server) == nil
	}()
	res, err := scenario.Soak(context.Background(), cfg)
	if err != nil {
		return err
	}
	haveServer := <-statsDone
	if *jsonOut != "" {
		b, _ := json.Marshal(map[string]any{"soak": res, "object_requests": during, "server": server}, jsontext.WithIndent("  "), json.Deterministic(true))
		if err := os.WriteFile(*jsonOut, b, 0o644); err != nil {
			return err
		}
	}
	printSoak(res)
	if haveServer {
		printRemoteStats(&server)
	}
	if counted {
		printCounts(during, res.Acked)
	}
	if len(res.Violations) > 0 {
		return fmt.Errorf("%d violations", len(res.Violations))
	}
	return nil
}

func printCounts(c fakegcs.Counts, writes int) {
	slog.Info("object requests during load", "get", c.Get, "list", c.List, "create", c.Create, "delete", c.Delete, "mib_in", float64(c.BytesIn)/(1<<20), "mib_out", float64(c.BytesOut)/(1<<20))
	if writes > 0 {
		slog.Info("object requests per acknowledged write", "class_a", float64(c.Create+c.List)/float64(writes), "class_b", float64(c.Get)/float64(writes))
	}
}

func printSoak(r *scenario.SoakResult) {
	if r.Integrity == "skipped" {
		slog.Info("acknowledged writes", "acked", r.Acked)
	} else {
		slog.Info("acknowledged writes", "acked", r.Acked, "items", r.Items)
	}
	slog.Info("write latency", "p50_ms", r.WriteLatency.P50, "p90_ms", r.WriteLatency.P90, "p99_ms", r.WriteLatency.P99, "max_ms", r.WriteLatency.Max)
	slog.Info("read latency", "p50_ms", r.ReadLatency.P50, "p90_ms", r.ReadLatency.P90, "p99_ms", r.ReadLatency.P99, "max_ms", r.ReadLatency.Max, "reads", r.ReadLatency.Count)
	keys := make([]string, 0, len(r.Statuses))
	for k := range r.Statuses {
		keys = append(keys, k)
	}
	slices.Sort(keys)
	for _, k := range keys {
		slog.Info("status", "status", k, "count", r.Statuses[k])
	}
	slog.Info("chaos", "crashes", r.Crashes, "scale_to_zeros", r.ScaleToZeros, "deploys", r.Deploys, "instances", len(r.Instances))
	if len(r.Instances) > 0 {
		exits := map[string]int{}
		var peakRSS, peakDisk int64
		var ready []float64
		for _, in := range r.Instances {
			exits[in.Exit]++
			peakRSS = max(peakRSS, in.PeakRSS)
			peakDisk = max(peakDisk, in.PeakDisk)
			ready = append(ready, in.ReadyMillis)
		}
		slices.Sort(ready)
		slog.Info("instances", "exits", exits, "peak_rss_mib", float64(peakRSS)/(1<<20), "peak_scratch_mib", float64(peakDisk)/(1<<20))
		slog.Info("instance start to listen", "median_ms", ready[len(ready)/2], "max_ms", ready[len(ready)-1])
	}
	slog.Info("overlap", "stale_reads", r.StaleReads)
	slog.Info("after restart", "missing", r.Missing, "mismatched", r.Mismatched, "integrity", r.Integrity)
	n := min(len(r.Violations), 10)
	slog.Info("violations", "count", len(r.Violations))
	for _, v := range r.Violations[:n] {
		slog.Info("violation", "detail", v)
	}
	if len(r.Violations) > n {
		slog.Info("violations truncated", "more", len(r.Violations)-n)
	}
}

// live runs the soak workload against a service that is already up, then
// reads every acknowledged write back. -roll starts a new Cloud Run
// revision first so the read-back comes from the replica.
func live(args []string) error {
	cfg := scenario.SoakConfig{}
	fs := flag.NewFlagSet("live", flag.ExitOnError)
	base := fs.String("url", "", "base URL of the running service")
	fs.DurationVar(&cfg.Duration, "duration", time.Minute, "how long to run")
	fs.IntVar(&cfg.Writers, "writers", 8, "concurrent writers")
	fs.IntVar(&cfg.Readers, "readers", 8, "concurrent readers")
	fs.IntVar(&cfg.BodySize, "body-size", 200, "bytes per item")
	fs.DurationVar(&cfg.WriteInterval, "write-interval", 0, "pause between each writer's writes (0 writes as fast as possible)")
	admin := fs.String("admin-token", "", "bearer token for GET /admin/check (optional)")
	roll := fs.Bool("roll", false, "deploy a new Cloud Run revision before reading writes back")
	project := fs.String("project", "", "Google Cloud project, required with -roll")
	region := fs.String("region", "us-central1", "Cloud Run region")
	service := fs.String("service", "cloudrun-duckdb", "Cloud Run service name")
	jsonOut := fs.String("json", "", "write the result as JSON to this file")
	fs.Parse(args)
	if *base == "" {
		return errors.New("-url is required")
	}
	if *roll && *project == "" {
		return errors.New("-roll requires -project")
	}
	*base = strings.TrimRight(*base, "/")
	cfg.URL = *base
	cfg.AdminToken = *admin

	var during remoteStats
	var haveDuring bool
	var cold *liveCold
	cfg.BeforeVerify = func(ctx context.Context) error {
		client := &http.Client{Timeout: 30 * time.Second}
		if err := getJSON(client, *base+"/stats", &during); err != nil {
			slog.Warn("stats before read-back", "err", err)
		} else {
			haveDuring = true
		}
		if !*roll {
			return nil
		}
		c, err := rollService(ctx, *project, *region, *service, *base, during.Instance)
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
		printRemoteStats(&during)
	}
	if cold != nil {
		slog.Info("new instance", "instance", cold.Instance, "request_ms", cold.RequestMS, "open_ms", cold.OpenMS)
	}
	if *jsonOut != "" && res != nil {
		b, _ := json.Marshal(map[string]any{"soak": res, "during": during, "cold": cold}, jsontext.WithIndent("  "), json.Deterministic(true))
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
		Snapshots  int64   `json:"snapshots"`
		BaseBytes  int64   `json:"base_bytes"`
		ReadWait   pct     `json:"read_wait"`
		ReadQuery  pct     `json:"read_query"`
		WriteQueue pct     `json:"write_queue"`
		Tx         pct     `json:"tx"`
		Flush      pct     `json:"flush"`
		Write      pct     `json:"write"`
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
	slog.Info("server during load", "instance", st.Instance, "open_ms", s.OpenMS, "writes", s.Writes, "batches", s.Batches, "conflicts", s.Conflicts, "snapshots", s.Snapshots, "base_bytes", s.BaseBytes)
	for _, p := range []struct {
		name string
		p    pct
	}{
		{"read wait", s.ReadWait}, {"read query", s.ReadQuery}, {"write queue", s.WriteQueue},
		{"duckdb tx", s.Tx}, {"flush", s.Flush}, {"write ack", s.Write},
		{"replica get", s.GCS.Get}, {"replica list", s.GCS.List}, {"replica put", s.GCS.Put},
	} {
		slog.Info(p.name, "n", p.p.Count, "p50_ms", p.p.P50, "p90_ms", p.p.P90, "p99_ms", p.p.P99, "max_ms", p.p.Max)
	}
}

// rollService deploys a new revision and waits until /stats reports a
// different instance.
func rollService(ctx context.Context, project, region, service, base, oldInstance string) (*liveCold, error) {
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
		err := getJSON(client, base+"/stats", &st)
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
	BaseBytes    int64   `json:"base_bytes"`
	ListenMillis float64 `json:"start_to_listen_ms"`
	FirstMillis  float64 `json:"first_request_ms"`
	OpenMillis   float64 `json:"open_ms"`
	WarmP50      float64 `json:"random_read_p50_ms"`
	WarmP99      float64 `json:"random_read_p99_ms"`
	PeakRSS      int64   `json:"peak_rss_bytes"`
	PeakScratch  int64   `json:"peak_scratch_bytes"`
	SeedMillis   float64 `json:"seed_ms"`
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
		u := withPath(c.replicaURL, "rows-"+strconv.Itoa(rows))
		var seedMS float64
		if !*skipSeed {
			start := time.Now()
			cmd := exec.Command(c.app, "seed", "-replica-url", u, "-rows", strconv.Itoa(rows), "-row-size", "1000", "-force")
			cmd.Env = append(os.Environ(), c.env...)
			cmd.Stdout, cmd.Stderr = os.Stderr, os.Stderr
			if err := cmd.Run(); err != nil {
				return fmt.Errorf("seed %d rows: %w", rows, err)
			}
			seedMS = ms(time.Since(start))
		}
		r, err := measureSize(&c, u, rows, *trials, *reads)
		if err != nil {
			return err
		}
		r.SeedMillis = seedMS
		results = append(results, r)
	}

	for _, r := range results {
		slog.Info("cold start", "rows", r.Rows, "base_mib", float64(r.BaseBytes)/(1<<20), "listen_ms", r.ListenMillis, "first_ms", r.FirstMillis, "open_ms", r.OpenMillis,
			"warm_p50_ms", r.WarmP50, "warm_p99_ms", r.WarmP99, "peak_rss_mib", float64(r.PeakRSS)/(1<<20), "peak_scratch_mib", float64(r.PeakScratch)/(1<<20))
	}
	if *jsonOut != "" {
		b, _ := json.Marshal(results, jsontext.WithIndent("  "), json.Deterministic(true))
		return os.WriteFile(*jsonOut, b, 0o644)
	}
	return nil
}

func measureSize(c *common, replicaURL string, rows, trials, reads int) (coldResult, error) {
	res := coldResult{Rows: rows}
	sim, srv, done, err := c.sim(replicaURL)
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
				BaseBytes  int64   `json:"base_bytes"`
			} `json:"store"`
		}
		if err := getJSON(client, srv.URL+"/stats", &st); err != nil {
			return res, err
		}
		open = append(open, st.Store.OpenMillis)
		res.BaseBytes = st.Store.BaseBytes

		for range reads {
			start := time.Now()
			if err := getJSON(client, srv.URL+"/items/"+strconv.Itoa(1+rand.IntN(rows)), nil); err != nil {
				return res, err
			}
			warm = append(warm, ms(time.Since(start)))
		}
	}
	sim.ScaleToZero()
	for _, in := range sim.Instances() {
		res.PeakRSS = max(res.PeakRSS, in.PeakRSS)
		res.PeakScratch = max(res.PeakScratch, in.PeakDisk)
	}
	res.ListenMillis = median(listen)
	res.FirstMillis = median(first)
	res.OpenMillis = median(open)
	slices.Sort(warm)
	res.WarmP50 = warm[len(warm)/2]
	res.WarmP99 = warm[len(warm)*99/100]
	return res, nil
}

func getJSON(client *http.Client, u string, into any) error {
	resp, err := client.Get(u)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		return err
	}
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("GET %s: %d %s", u, resp.StatusCode, b)
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
