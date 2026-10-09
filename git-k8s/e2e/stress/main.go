// Command stress pushes bursts of branches to repositories that git-k8s
// manages, plays their developers and reviewers, and records how the
// branches move through checks and merge queues. setup.sh starts what it
// runs against. See README.md.
package main

import (
	"bufio"
	"context"
	"errors"
	"flag"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"runtime"
	"strings"
	"syscall"
	"time"
)

const usage = `usage: stress COMMAND [flags]

Commands:
  run      run a scenario, then analyze it
  analyze  analyze a run's records again
  verify   verify a finished run again, then analyze it
  chart    draw charts of one or more runs
  report   write a table that compares runs
  cleanup  delete scenario namespaces

Run "stress COMMAND -h" for a command's flags.
`

func main() {
	if len(os.Args) < 2 {
		fmt.Fprint(os.Stderr, usage)
		os.Exit(2)
	}
	commands := map[string]func([]string) error{
		"run": runCmd, "analyze": analyzeCmd, "verify": verifyCmd, "chart": chartCmd, "report": reportCmd, "cleanup": cleanupCmd,
	}
	cmd, ok := commands[os.Args[1]]
	if !ok {
		fmt.Fprint(os.Stderr, usage)
		os.Exit(2)
	}
	if err := cmd(os.Args[2:]); err != nil {
		logf("%v", err)
		os.Exit(1)
	}
}

func logf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "%s %s\n", time.Now().Format("15:04:05.000"), fmt.Sprintf(format, args...))
}

func numCPU() int { return runtime.NumCPU() }

func defaultState() string {
	if s := os.Getenv("GK_STRESS_STATE"); s != "" {
		return s
	}
	return "/tmp/gk-stress"
}

// loadEnv reads the KEY=VALUE lines that setup.sh writes.
func loadEnv(path string) (map[string]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("%w; run setup.sh first", err)
	}
	defer f.Close()
	env := map[string]string{}
	s := bufio.NewScanner(f)
	for s.Scan() {
		line := strings.TrimSpace(s.Text())
		if k, v, ok := strings.Cut(line, "="); ok && !strings.HasPrefix(line, "#") {
			env[k] = strings.Trim(v, `"'`)
		}
	}
	for _, k := range []string{"STATE", "CLUSTER", "CONTEXT", "PASSWORD", "CLUSTER_URL", "HOST_URL", "MOD_PORT"} {
		if env[k] == "" {
			return nil, fmt.Errorf("%s doesn't set %s; run setup.sh again", path, k)
		}
	}
	return env, s.Err()
}

func runCmd(args []string) error {
	fs := flag.NewFlagSet("run", flag.ExitOnError)
	scenario := fs.String("scenario", "clean", "clean, mixed, landing, parallel, nogotest, big, or poll30")
	n := fs.Int("n", 0, "branches per repository, or 0 for the scenario's default")
	repos := fs.Int("repos", 0, "repositories, or 0 for the scenario's default")
	poll := fs.String("poll", "2s", `each Repository object's pollInterval, or "default" to leave it out (30s); poll30 always leaves it out`)
	out := fs.String("out", "", "directory for the run's records (default STATE/runs/SCENARIO-TIME)")
	state := fs.String("state", defaultState(), "the directory that setup.sh wrote, which GK_STRESS_STATE also sets")
	stagger := fs.Duration("stagger", -1, "time between first pushes, or -1 for the scenario's default")
	approveDelay := fs.Duration("approve-delay", 15*time.Second, "how long the reviewer waits to approve a high-risk head")
	timeout := fs.Duration("timeout", 0, "how long the burst may take, or 0 for the scenario's default")
	warmup := fs.Bool("warmup", true, "land one branch in each repository before the burst")
	_ = fs.Parse(args)

	env, err := loadEnv(filepath.Join(*state, "env"))
	if err != nil {
		return err
	}
	pollInterval := *poll
	if pollInterval == "default" {
		pollInterval = ""
	}
	p, err := buildPlan(*scenario, *n, *repos, pollInterval)
	if err != nil {
		return err
	}
	if *stagger >= 0 {
		p.Stagger = stagger.String()
	}
	p.ApproveDelay = approveDelay.String()
	if *timeout > 0 {
		p.Timeout = timeout.String()
	}
	p.Warmup = *warmup
	if *out == "" {
		*out = filepath.Join(*state, "runs", p.Scenario+"-"+time.Now().Format("20060102-150405"))
	}
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()
	logf("recording to %s", *out)
	runErr := runScenario(ctx, env, p, *out)
	if err := analyze(*out); err != nil {
		runErr = errors.Join(runErr, fmt.Errorf("analyzing %s: %w", *out, err))
	} else {
		logf("wrote %s", filepath.Join(*out, "summary.md"))
	}
	return runErr
}

func analyzeCmd(args []string) error {
	fs := flag.NewFlagSet("analyze", flag.ExitOnError)
	_ = fs.Parse(args)
	if fs.NArg() == 0 {
		return errors.New("usage: stress analyze RUN_DIR...")
	}
	var errs []error
	for _, dir := range fs.Args() {
		if err := analyze(dir); err != nil {
			errs = append(errs, fmt.Errorf("%s: %w", dir, err))
		}
	}
	return errors.Join(errs...)
}

// verifyCmd checks finished runs again. The git server and module proxy
// that setup.sh started must still run, with the runs' repositories.
func verifyCmd(args []string) error {
	fs := flag.NewFlagSet("verify", flag.ExitOnError)
	state := fs.String("state", defaultState(), "the directory that setup.sh wrote")
	_ = fs.Parse(args)
	if fs.NArg() == 0 {
		return errors.New("usage: stress verify RUN_DIR...")
	}
	env, err := loadEnv(filepath.Join(*state, "env"))
	if err != nil {
		return err
	}
	var errs []error
	for _, dir := range fs.Args() {
		if err := reverify(env, dir); err != nil {
			errs = append(errs, fmt.Errorf("%s: %w", dir, err))
		}
	}
	return errors.Join(errs...)
}

// cleanupCmd deletes the namespaces of earlier scenarios, so that their
// Repository objects stop polling, and waits for them to go away.
func cleanupCmd(args []string) error {
	fs := flag.NewFlagSet("cleanup", flag.ExitOnError)
	state := fs.String("state", defaultState(), "the directory that setup.sh wrote")
	keep := fs.String("keep", "", "a namespace to keep")
	wait := fs.Duration("wait", 5*time.Minute, "how long to wait for the namespaces to go away")
	_ = fs.Parse(args)
	env, err := loadEnv(filepath.Join(*state, "env"))
	if err != nil {
		return err
	}
	k, err := newKubeClient(env["CONTEXT"])
	if err != nil {
		return err
	}
	ctx := context.Background()
	list := func() ([]string, error) {
		var nss struct {
			Items []struct {
				Metadata objectMeta `json:"metadata"`
			} `json:"items"`
		}
		if err := k.get(ctx, "/api/v1/namespaces", &nss); err != nil {
			return nil, err
		}
		var names []string
		for _, ns := range nss.Items {
			if strings.HasPrefix(ns.Metadata.Name, "stress-") && ns.Metadata.Name != *keep {
				names = append(names, ns.Metadata.Name)
			}
		}
		return names, nil
	}
	names, err := list()
	if err != nil {
		return err
	}
	for _, name := range names {
		logf("deleting namespace %s", name)
		if err := k.delete(ctx, "/api/v1/namespaces/"+name); err != nil {
			return err
		}
	}
	deadline := time.Now().Add(*wait)
	for {
		left, err := list()
		if err != nil {
			return err
		}
		if len(left) == 0 {
			return nil
		}
		if time.Now().After(deadline) {
			return fmt.Errorf("namespaces still exist after %s: %s", *wait, strings.Join(left, ", "))
		}
		time.Sleep(time.Second)
	}
}
