// Package scenario drives cloudrun-sqlite through a Cloud Run simulator
// with concurrent readers and writers while instances crash, scale to zero,
// and overlap during deploys, then checks that every acknowledged write
// survived.
package scenario

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"math/rand/v2"
	"net/http"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/crsim"
)

// SoakConfig configures Soak.
type SoakConfig struct {
	URL      string     // base URL of the simulated service
	Sim      *crsim.Sim // used for chaos actions
	Duration time.Duration
	Writers  int
	Readers  int
	BodySize int
	// WriteInterval paces each writer. Zero writes as fast as possible.
	WriteInterval time.Duration

	CrashEvery  time.Duration // SIGKILL the instance (0 disables)
	ScaleEvery  time.Duration // SIGTERM the instance, as when idle (0 disables)
	DeployEvery time.Duration // start a new revision (0 disables)
	Overlap     time.Duration // how long both revisions serve during a deploy

	// StaleWindow is how long after an acknowledged write a 404 for it
	// counts as a stale read rather than a lost write. An instance that
	// opened before the write sees it on its next poll.
	StaleWindow time.Duration

	// AdminToken is the server's ADMIN_TOKEN, for the final integrity check.
	// An empty token skips that check.
	AdminToken string

	// BeforeVerify runs after the load stops and before every acknowledged
	// write is read back. The live benchmark uses it to snapshot /stats and
	// to start a new Cloud Run instance first.
	BeforeVerify func(ctx context.Context) error
}

// Latency summarizes request latencies in milliseconds.
type Latency struct {
	Count int     `json:"count"`
	P50   float64 `json:"p50_ms"`
	P90   float64 `json:"p90_ms"`
	P99   float64 `json:"p99_ms"`
	Max   float64 `json:"max_ms"`
}

// SoakResult reports what happened.
type SoakResult struct {
	Acked        int            `json:"acked_writes"`
	WriteLatency Latency        `json:"write_latency"`
	ReadLatency  Latency        `json:"read_latency"`
	Statuses     map[string]int `json:"statuses"`
	StaleReads   int            `json:"stale_reads"`
	Violations   []string       `json:"violations"`
	Crashes      int            `json:"crashes"`
	ScaleToZeros int            `json:"scale_to_zeros"`
	Deploys      int            `json:"deploys"`

	Missing    int    `json:"missing_after_restart"`
	Mismatched int    `json:"mismatched_after_restart"`
	Integrity  string `json:"integrity"`
	Items      int64  `json:"items"`

	Instances []crsim.InstanceStats `json:"instances"`
}

type ack struct {
	body string
	at   time.Time
}

type recorder struct {
	mu       sync.Mutex
	writes   []time.Duration
	reads    []time.Duration
	statuses map[string]int
}

func (r *recorder) status(kind string, code int, err error) {
	key := kind + " " + strconv.Itoa(code)
	if err != nil {
		key = kind + " error"
	}
	r.mu.Lock()
	r.statuses[key]++
	r.mu.Unlock()
}

// Soak runs the scenario and verifies the result.
func Soak(ctx context.Context, cfg SoakConfig) (*SoakResult, error) {
	if cfg.BodySize == 0 {
		cfg.BodySize = 200
	}
	if cfg.StaleWindow == 0 {
		cfg.StaleWindow = 5 * time.Second
	}
	client := &http.Client{Timeout: time.Minute}
	rec := &recorder{statuses: map[string]int{}}
	res := &SoakResult{}

	var (
		mu         sync.Mutex
		acked      = map[int64]ack{}
		ids        []int64
		violations []string
		stale      atomic.Int64
	)
	violate := func(format string, args ...any) {
		msg := fmt.Sprintf(format, args...)
		mu.Lock()
		violations = append(violations, msg)
		mu.Unlock()
		slog.InfoContext(ctx, "violation", "msg", msg)
	}

	runCtx, cancel := context.WithTimeout(ctx, cfg.Duration)
	defer cancel()
	var wg sync.WaitGroup

	for w := range cfg.Writers {
		wg.Go(func() {
			for seq := 0; runCtx.Err() == nil; seq++ {
				body := fmt.Sprintf("w%d-%d-%s", w, seq, strings.Repeat("x", cfg.BodySize))
				start := time.Now()
				code, data, err := do(runCtx, client, http.MethodPost, cfg.URL+"/items", body)
				if runCtx.Err() != nil {
					return
				}
				rec.status("POST", code, err)
				if err != nil || code != http.StatusCreated {
					time.Sleep(20 * time.Millisecond)
					continue
				}
				d := time.Since(start)
				var out struct{ ID int64 }
				if err := json.Unmarshal(data, &out); err != nil {
					violate("bad create response %q", data)
					continue
				}
				mu.Lock()
				if _, dup := acked[out.ID]; dup {
					violations = append(violations, fmt.Sprintf("id %d acknowledged twice", out.ID))
				}
				acked[out.ID] = ack{body: body, at: time.Now()}
				ids = append(ids, out.ID)
				mu.Unlock()
				rec.mu.Lock()
				rec.writes = append(rec.writes, d)
				rec.mu.Unlock()
				if rest := cfg.WriteInterval - d; rest > 0 {
					time.Sleep(rest)
				}
			}
		})
	}

	for range cfg.Readers {
		wg.Go(func() {
			for runCtx.Err() == nil {
				mu.Lock()
				if len(ids) == 0 {
					mu.Unlock()
					time.Sleep(10 * time.Millisecond)
					continue
				}
				id := ids[rand.IntN(len(ids))]
				want := acked[id]
				mu.Unlock()
				start := time.Now()
				code, data, err := do(runCtx, client, http.MethodGet, cfg.URL+"/items/"+strconv.FormatInt(id, 10), "")
				if runCtx.Err() != nil {
					return
				}
				rec.status("GET", code, err)
				switch {
				case err != nil:
					time.Sleep(20 * time.Millisecond)
				case code == http.StatusOK:
					rec.mu.Lock()
					rec.reads = append(rec.reads, time.Since(start))
					rec.mu.Unlock()
					var out struct{ Body string }
					if json.Unmarshal(data, &out) != nil || out.Body != want.body {
						violate("id %d read back %.40q, want %.40q", id, out.Body, want.body)
					}
				case code == http.StatusNotFound:
					if time.Since(want.at) < cfg.StaleWindow {
						stale.Add(1)
					} else {
						violate("id %d acknowledged %s ago is missing", id, time.Since(want.at).Round(time.Millisecond))
					}
				}
			}
		})
	}

	chaos := func(every time.Duration, name string, counter *int, fn func()) {
		if every <= 0 {
			return
		}
		wg.Go(func() {
			t := time.NewTicker(every)
			defer t.Stop()
			for {
				select {
				case <-runCtx.Done():
					return
				case <-t.C:
					slog.InfoContext(runCtx, "chaos", "action", name)
					fn()
					mu.Lock()
					*counter++
					mu.Unlock()
				}
			}
		})
	}
	if cfg.Sim != nil {
		chaos(cfg.CrashEvery, "crash", &res.Crashes, cfg.Sim.Crash)
		chaos(cfg.ScaleEvery, "scale to zero", &res.ScaleToZeros, cfg.Sim.ScaleToZero)
		chaos(cfg.DeployEvery, "deploy", &res.Deploys, func() {
			if err := cfg.Sim.Deploy(runCtx, cfg.Overlap); err != nil {
				slog.ErrorContext(runCtx, "deploy", "err", err)
			}
		})
	}
	wg.Wait()

	// Restart from nothing and check every acknowledged write. A live
	// service has no simulator; BeforeVerify can roll a new instance instead.
	if cfg.Sim != nil {
		cfg.Sim.ScaleToZero()
	}
	if cfg.BeforeVerify != nil {
		if err := cfg.BeforeVerify(ctx); err != nil {
			return nil, err
		}
	}
	mu.Lock()
	all := slices.Clone(ids)
	mu.Unlock()
	res.Acked = len(all)
	var missing, mismatched atomic.Int64
	work := make(chan int64)
	var vwg sync.WaitGroup
	for range 16 {
		vwg.Go(func() {
			for id := range work {
				code, data, err := do(ctx, client, http.MethodGet, cfg.URL+"/items/"+strconv.FormatInt(id, 10), "")
				var out struct{ Body string }
				switch {
				case err != nil || code == http.StatusNotFound:
					missing.Add(1)
					violate("id %d missing after restart (code %d, err %v)", id, code, err)
				case json.Unmarshal(data, &out) != nil || out.Body != acked[id].body:
					mismatched.Add(1)
					violate("id %d wrong after restart", id)
				}
			}
		})
	}
	for _, id := range all {
		work <- id
	}
	close(work)
	vwg.Wait()
	res.Missing = int(missing.Load())
	res.Mismatched = int(mismatched.Load())

	if cfg.AdminToken == "" {
		res.Integrity = "skipped"
	} else {
		code, data, err := do(ctx, client, http.MethodGet, cfg.URL+"/admin/check", "", "Bearer "+cfg.AdminToken)
		if err != nil || code != http.StatusOK {
			return nil, fmt.Errorf("integrity check: %d %v %s", code, err, data)
		}
		var check struct {
			Integrity string
			Items     int64
		}
		if err := json.Unmarshal(data, &check); err != nil {
			return nil, err
		}
		res.Integrity = check.Integrity
		res.Items = check.Items
		if check.Integrity != "ok" {
			violate("integrity_check: %s", check.Integrity)
		}
		if check.Items < int64(res.Acked) {
			violate("%d items in database, %d acknowledged", check.Items, res.Acked)
		}
	}

	res.WriteLatency = summarize(rec.writes)
	res.ReadLatency = summarize(rec.reads)
	res.Statuses = rec.statuses
	res.StaleReads = int(stale.Load())
	res.Violations = violations
	if cfg.Sim != nil {
		res.Instances = cfg.Sim.Instances()
	}
	return res, nil
}

func do(ctx context.Context, client *http.Client, method, url, body string, auth ...string) (int, []byte, error) {
	var rd io.Reader
	if body != "" {
		rd = strings.NewReader(body)
	}
	req, err := http.NewRequestWithContext(ctx, method, url, rd)
	if err != nil {
		return 0, nil, err
	}
	for _, a := range auth {
		req.Header.Set("Authorization", a)
	}
	resp, err := client.Do(req)
	if err != nil {
		return 0, nil, err
	}
	defer resp.Body.Close()
	data, err := io.ReadAll(resp.Body)
	return resp.StatusCode, data, err
}

func summarize(ds []time.Duration) Latency {
	if len(ds) == 0 {
		return Latency{}
	}
	ds = slices.Clone(ds)
	slices.Sort(ds)
	at := func(q float64) float64 {
		return float64(ds[int(q*float64(len(ds)-1))].Microseconds()) / 1000
	}
	return Latency{Count: len(ds), P50: at(0.5), P90: at(0.9), P99: at(0.99), Max: at(1)}
}
