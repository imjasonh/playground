// Command runner is the build runner that a worker pod or a Substrate actor
// runs. It leases actions from the scheduler in cas with its tenant token,
// builds each action's exec root (on a host-mounted casfs inputs volume when
// it has one, else a lazy FUSE mount when the host allows it, else a copy
// from the node-local cascache), runs the command, and uploads the outputs
// and an ActionResult to cas. It runs until it is stopped, so a suspended
// actor resumes into a runner that leases again.
package main

import (
	"context"
	"errors"
	"flag"
	"log/slog"
	"os"
	"os/signal"
	"strings"
	"syscall"
	"time"

	_ "github.com/chainguard-dev/clog/gcp/init"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/bot"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

func main() {
	originAddr := flag.String("origin-addr", "", "cas address for leases, uploads, and the action cache (host:port)")
	cacheAddr := flag.String("cache-addr", "", "node-local cascache address for reads (host:port); defaults to -origin-addr")
	instances := flag.String("instances", "", "comma-separated instance names to lease from; empty means every instance the token allows")
	token := flag.String("token", "", "tenant token; under Substrate, the placeholder the egress gateway replaces")
	botID := flag.String("bot-id", "", "runner identity reported to the scheduler; defaults to the hostname")
	botIDFile := flag.String("bot-id-file", "", "file holding the runner identity, such as a Substrate actor_metadata name projection")
	workDir := flag.String("work-dir", "/tmp/ci-substrate", "directory for exec roots")
	inputMode := flag.String("input-mode", string(bot.InputAuto), "how inputs reach the exec root: volume, fuse, copy, or auto")
	inputsVolume := flag.String("inputs-volume", "", "mounted casfs inputs volume for the volume input mode, such as a Substrate external volume")
	leaseWait := flag.Duration("lease-wait", 20*time.Second, "how long each Lease call waits for a job")
	flag.Parse()

	if *originAddr == "" {
		slog.Error("missing required flag", "need", "-origin-addr")
		os.Exit(2)
	}
	id, err := identity(*botID, *botIDFile)
	if err != nil {
		slog.Error("runner identity", "err", err)
		os.Exit(2)
	}
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()
	shutdown, err := telemetry.Setup(ctx, "runner")
	if err != nil {
		slog.Error("setting up telemetry", "err", err)
		os.Exit(1)
	}
	defer func() {
		sctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		if err := shutdown(sctx); err != nil {
			slog.Error("flushing telemetry", "err", err)
		}
	}()
	dial := append(telemetry.DialOptions(), grpc.WithTransportCredentials(insecure.NewCredentials()))

	originConn, err := grpc.NewClient(*originAddr, dial...)
	if err != nil {
		slog.Error("dialing origin", "err", err)
		os.Exit(1)
	}
	defer originConn.Close()
	origin := remote.NewClient(originConn)
	cache := origin
	if *cacheAddr != "" && *cacheAddr != *originAddr {
		cacheConn, err := grpc.NewClient(*cacheAddr, dial...)
		if err != nil {
			slog.Error("dialing cache", "err", err)
			os.Exit(1)
		}
		defer cacheConn.Close()
		cache = remote.NewClient(cacheConn)
	}

	var names []string
	if *instances != "" {
		names = strings.Split(*instances, ",")
	}
	b, err := bot.New(bot.Config{
		BotID:        id,
		Token:        *token,
		Instances:    names,
		Worker:       workerv1.NewWorkerServiceClient(originConn),
		Origin:       origin,
		Cache:        cache,
		WorkDir:      *workDir,
		InputMode:    bot.InputMode(*inputMode),
		InputsVolume: *inputsVolume,
		LeaseWait:    *leaseWait,
	})
	if err != nil {
		slog.Error("configuring runner", "err", err)
		os.Exit(1)
	}
	slog.Info("runner leasing", "bot", id, "origin", *originAddr, "cache", *cacheAddr, "inputMode", b.InputMode())
	if err := b.Run(ctx); err != nil && !errors.Is(err, context.Canceled) {
		slog.Error("runner stopped", "err", err)
		os.Exit(1)
	}
}

// identity picks the bot id: the flag, else the file's contents, else the
// hostname.
func identity(id, file string) (string, error) {
	if id != "" {
		return id, nil
	}
	if file != "" {
		b, err := os.ReadFile(file)
		if err != nil {
			return "", err
		}
		if id := strings.TrimSpace(string(b)); id != "" {
			return id, nil
		}
		return "", errors.New("bot id file is empty")
	}
	return os.Hostname()
}
