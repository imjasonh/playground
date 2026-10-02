// Command bench measures what caches cost, comparing kube with client-go.
//
// It starts a control plane from the binaries in $KUBEBUILDER_ASSETS,
// creates Pods that look like those in a real cluster (Deployment labels,
// owner references, two containers, probes, volumes, and a kubelet-written
// status), and runs each cache configuration in a fresh process so their
// heaps don't mix. It also compares the bytes on the wire for full and
// metadata-only lists of Secrets, and the size of a controller binary.
//
//	cd kube/bench
//	KUBEBUILDER_ASSETS=/path/to/envtest go run . -pods 5000
package main

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/envtest"
	"github.com/imjasonh/playground/kube/k8s"
	"k8s.io/client-go/informers"
	"k8s.io/client-go/kubernetes"
	"k8s.io/client-go/tools/cache"
	"k8s.io/client-go/tools/clientcmd"
	crcache "sigs.k8s.io/controller-runtime/pkg/cache"
)

var (
	pods       = flag.Int("pods", 5000, "Pods to create")
	secrets    = flag.Int("secrets", 1000, "Secrets to create for the wire-size comparison")
	secretSize = flag.Int("secret-size", 8192, "bytes of data in each Secret")
	mode       = flag.String("mode", "", "run one measurement (used by child processes)")
	kubeconfig = flag.String("kubeconfig", "", "kubeconfig for -mode")
	namespace  = flag.String("namespace", "bench", "namespace for -mode")
	hold       = flag.Bool("hold", false, "after creating objects, keep the control plane running for experiments")
)

const ns = "bench"

type result struct {
	Mode    string  `json:"mode"`
	Objects int     `json:"objects"`
	Heap    uint64  `json:"heap"`
	Sync    float64 `json:"sync"`
}

func main() {
	flag.Parse()
	if *mode != "" {
		r, err := measure(*mode, *kubeconfig, *namespace)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		_ = json.NewEncoder(os.Stdout).Encode(r)
		return
	}
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

// probe times how long the API server takes to send the bench Pods, without
// decoding them: as a JSON streaming list, a JSON list, and a protobuf list.
// It separates the server's encoding time from the client's decoding time.
func probe(c *client.Client) error {
	ctx := context.Background()
	q := map[string][]string{"sendInitialEvents": {"true"}, "resourceVersionMatch": {"NotOlderThan"}, "allowWatchBookmarks": {"true"}}
	start := time.Now()
	w, err := c.Watch(ctx, client.Path("v1", "pods", ns, ""), q, "")
	if err != nil {
		return err
	}
	n := 0
	for {
		typ, frame, err := w.NextFrame()
		if err != nil {
			return err
		}
		n += len(frame)
		if typ == client.Bookmark && strings.Contains(string(frame), client.InitialEventsEndAnnotation) {
			break
		}
	}
	w.Close()
	fmt.Printf("Reading the streaming list without decoding: %.1f MiB in %v.\n", float64(n)/(1<<20), time.Since(start).Round(time.Millisecond))
	for _, accept := range []string{"application/json", "application/vnd.kubernetes.protobuf"} {
		start := time.Now()
		resp, err := c.Do(ctx, client.Request{Method: http.MethodGet, Path: client.Path("v1", "pods", ns, ""), Query: map[string][]string{"resourceVersion": {"0"}}, Accept: accept, Stream: true})
		if err != nil {
			return err
		}
		size, _ := io.Copy(io.Discard, resp.Body)
		resp.Body.Close()
		fmt.Printf("Reading a list as %s: %.1f MiB in %v.\n", accept, float64(size)/(1<<20), time.Since(start).Round(time.Millisecond))
	}
	fmt.Println()
	return nil
}

func run() error {
	ctx := context.Background()
	assets := os.Getenv("KUBEBUILDER_ASSETS")
	if assets == "" {
		return fmt.Errorf("set KUBEBUILDER_ASSETS to a directory with etcd and kube-apiserver")
	}
	env, err := envtest.Start(ctx, assets)
	if err != nil {
		return err
	}
	defer env.Stop()
	cfg, err := client.LoadKubeconfig([]string{env.Kubeconfig}, "")
	if err != nil {
		return err
	}
	c, err := client.New(cfg, "bench")
	if err != nil {
		return err
	}
	if err := c.Create(ctx, "/api/v1/namespaces", map[string]any{"apiVersion": "v1", "kind": "Namespace", "metadata": map[string]any{"name": ns}}, nil); err != nil {
		return err
	}
	start := time.Now()
	if err := seed(ctx, c); err != nil {
		return err
	}
	fmt.Printf("Created %d Pods and %d Secrets in %v.\n\n", *pods, *secrets, time.Since(start).Round(time.Second))
	if *hold {
		fmt.Printf("Holding the control plane open. KUBECONFIG=%s\n", env.Kubeconfig)
		select {}
	}

	resp, err := c.Do(ctx, client.Request{Method: http.MethodGet, Path: client.Path("v1", "pods", ns, ""), Stream: true})
	if err != nil {
		return err
	}
	n, _ := io.Copy(io.Discard, resp.Body)
	resp.Body.Close()
	fmt.Printf("Average Pod JSON size, including managedFields: %d bytes.\n\n", n/int64(*pods))
	if err := probe(c); err != nil {
		return err
	}

	self, err := os.Executable()
	if err != nil {
		return err
	}
	fmt.Println("| Cache | Objects | Heap | Per object | Sync |")
	fmt.Println("|---|---|---|---|---|")
	for _, m := range []string{"client-go", "client-go-strip-managed-fields", "kube-k8s.Pod", "kube-k8s.Pod-paginated", "kube-k8s.Pod-no-interning", "kube-small-projection", "kube-metadata-only"} {
		out, err := exec.Command(self, "-mode", m, "-kubeconfig", env.Kubeconfig, "-namespace", ns).Output() // #nosec G204 -- runs this program.
		if err != nil {
			return fmt.Errorf("%s: %w", m, err)
		}
		var r result
		if err := json.Unmarshal(out, &r); err != nil {
			return fmt.Errorf("%s: %w: %s", m, err, out)
		}
		fmt.Printf("| %s | %d | %.1f MiB | %.0f B | %.2fs |\n", r.Mode, r.Objects, float64(r.Heap)/(1<<20), float64(r.Heap)/float64(r.Objects), r.Sync)
	}

	full, err := listBytes(ctx, c, "")
	if err != nil {
		return err
	}
	meta, err := listBytes(ctx, c, "application/json;as=PartialObjectMetadataList;g=meta.k8s.io;v=v1,application/json")
	if err != nil {
		return err
	}
	fmt.Printf("\nListing %d Secrets of %d bytes each: %.1f MiB full, %.2f MiB metadata-only.\n\n", *secrets, *secretSize, float64(full)/(1<<20), float64(meta)/(1<<20))
	return sizes()
}

func listBytes(ctx context.Context, c *client.Client, accept string) (int64, error) {
	resp, err := c.Do(ctx, client.Request{Method: http.MethodGet, Path: client.Path("v1", "secrets", ns, ""), Accept: accept, Stream: true})
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	return io.Copy(io.Discard, resp.Body)
}

// sizes builds the website example and an equivalent controller-runtime
// controller, and reports their sizes and module counts.
func sizes() error {
	dir, err := os.MkdirTemp("", "bench-bin-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(dir)
	fmt.Println("| Binary | Size (stripped) | Modules |")
	fmt.Println("|---|---|---|")
	for _, b := range []struct{ name, dir, pkg string }{
		{"kube (examples/website)", "..", "./examples/website"},
		{"controller-runtime (crsize)", ".", "./crsize"},
	} {
		out := filepath.Join(dir, "bin")
		cmd := exec.Command("go", "build", "-trimpath", "-ldflags=-s -w", "-o", out, b.pkg) // #nosec G204 -- fixed arguments.
		cmd.Dir = b.dir
		if msg, err := cmd.CombinedOutput(); err != nil {
			return fmt.Errorf("building %s: %w\n%s", b.name, err, msg)
		}
		st, err := os.Stat(out)
		if err != nil {
			return err
		}
		mods := exec.Command("go", "list", "-deps", "-f", "{{with .Module}}{{.Path}}{{end}}", b.pkg) // #nosec G204 -- fixed arguments.
		mods.Dir = b.dir
		list, err := mods.Output()
		if err != nil {
			return err
		}
		set := map[string]bool{}
		for _, m := range strings.Fields(string(list)) {
			set[m] = true
		}
		fmt.Printf("| %s | %.1f MiB | %d |\n", b.name, float64(st.Size())/(1<<20), len(set))
	}
	return nil
}

func randHex(n int) string {
	b := make([]byte, n)
	_, _ = rand.Read(b)
	return hex.EncodeToString(b)
}

// seed creates Pods shaped like a Deployment's, with a status written by a
// separate field manager as the kubelet would, and Secrets.
func seed(ctx context.Context, c *client.Client) error {
	work := make(chan int)
	errs := make(chan error, 1)
	var wg sync.WaitGroup
	for range 32 {
		wg.Go(func() {
			for i := range work {
				if err := seedOne(ctx, c, i); err != nil {
					select {
					case errs <- err:
					default:
					}
				}
			}
		})
	}
	for i := range max(*pods, *secrets) {
		work <- i
	}
	close(work)
	wg.Wait()
	select {
	case err := <-errs:
		return err
	default:
		return nil
	}
}

func seedOne(ctx context.Context, c *client.Client, i int) error {
	if i < *secrets {
		data := make([]byte, *secretSize)
		_, _ = rand.Read(data)
		if err := c.Create(ctx, client.Path("v1", "secrets", ns, ""), map[string]any{
			"apiVersion": "v1", "kind": "Secret", "metadata": map[string]any{"name": fmt.Sprintf("secret-%05d", i)},
			"data": map[string][]byte{"key": data},
		}, nil); err != nil {
			return err
		}
	}
	if i >= *pods {
		return nil
	}
	app := fmt.Sprintf("service-%03d", i/50)
	hash := randHex(5)
	name := fmt.Sprintf("%s-%s-%s", app, hash, randHex(3))
	env := []any{}
	for _, k := range []string{"LOG_LEVEL", "PORT", "DB_HOST", "DB_NAME", "CACHE_URL", "REGION", "FEATURE_FLAGS", "OTEL_EXPORTER_OTLP_ENDPOINT"} {
		env = append(env, map[string]any{"name": k, "value": strings.ToLower(k) + "-value"})
	}
	pod := map[string]any{
		"apiVersion": "v1", "kind": "Pod",
		"metadata": map[string]any{
			"name": name,
			"labels": map[string]string{
				"app.kubernetes.io/name": app, "app.kubernetes.io/instance": app + "-prod", "app.kubernetes.io/component": "backend",
				"app.kubernetes.io/part-of": "shop", "pod-template-hash": hash, "team": "payments",
			},
			"annotations": map[string]string{
				"kubectl.kubernetes.io/restartedAt": "2026-09-30T12:00:00Z", "prometheus.io/scrape": "true", "prometheus.io/port": "9090",
			},
			"ownerReferences": []any{map[string]any{
				"apiVersion": "apps/v1", "kind": "ReplicaSet", "name": app + "-" + hash,
				"uid": randHex(4) + "-" + randHex(2) + "-" + randHex(2) + "-" + randHex(2) + "-" + randHex(6), "controller": true, "blockOwnerDeletion": true,
			}},
		},
		"spec": map[string]any{
			"serviceAccountName": app,
			"nodeName":           fmt.Sprintf("node-%03d", i%100),
			"containers": []any{
				map[string]any{
					"name": "app", "image": "registry.example.com/shop/" + app + ":v1.42.0",
					"ports":          []any{map[string]any{"name": "http", "containerPort": 8080}, map[string]any{"name": "metrics", "containerPort": 9090}},
					"env":            env,
					"resources":      map[string]any{"requests": map[string]string{"cpu": "250m", "memory": "256Mi"}, "limits": map[string]string{"memory": "512Mi"}},
					"readinessProbe": map[string]any{"httpGet": map[string]any{"path": "/readyz", "port": "http"}, "periodSeconds": 5},
					"livenessProbe":  map[string]any{"httpGet": map[string]any{"path": "/healthz", "port": "http"}, "periodSeconds": 10},
					"volumeMounts":   []any{map[string]any{"name": "config", "mountPath": "/etc/app"}, map[string]any{"name": "tls", "mountPath": "/etc/tls", "readOnly": true}},
				},
				map[string]any{
					"name": "proxy", "image": "registry.example.com/mesh/proxy:v1.24.3",
					"args":      []string{"proxy", "sidecar", "--log-level=warn"},
					"resources": map[string]any{"requests": map[string]string{"cpu": "50m", "memory": "64Mi"}},
				},
			},
			"volumes": []any{
				map[string]any{"name": "config", "configMap": map[string]string{"name": app + "-config"}},
				map[string]any{"name": "tls", "secret": map[string]string{"secretName": app + "-tls"}},
			},
			"tolerations": []any{
				map[string]any{"key": "node.kubernetes.io/not-ready", "operator": "Exists", "effect": "NoExecute", "tolerationSeconds": 300},
				map[string]any{"key": "node.kubernetes.io/unreachable", "operator": "Exists", "effect": "NoExecute", "tolerationSeconds": 300},
			},
		},
	}
	path := client.Path("v1", "pods", ns, "")
	if err := c.Create(ctx, path, pod, nil); err != nil {
		return err
	}
	ts := "2026-10-01T08:00:00Z"
	status := map[string]any{"status": map[string]any{
		"phase": "Running", "hostIP": "10.0.1.7", "podIP": "10.244.3.17", "podIPs": []any{map[string]string{"ip": "10.244.3.17"}}, "startTime": ts, "qosClass": "Burstable",
		"conditions": []any{
			map[string]any{"type": "PodReadyToStartContainers", "status": "True", "lastTransitionTime": ts},
			map[string]any{"type": "Initialized", "status": "True", "lastTransitionTime": ts},
			map[string]any{"type": "Ready", "status": "True", "lastTransitionTime": ts},
			map[string]any{"type": "ContainersReady", "status": "True", "lastTransitionTime": ts},
			map[string]any{"type": "PodScheduled", "status": "True", "lastTransitionTime": ts},
		},
		"containerStatuses": []any{
			map[string]any{"name": "app", "ready": true, "started": true, "restartCount": 0, "image": "registry.example.com/shop/" + app + ":v1.42.0",
				"imageID": "registry.example.com/shop/" + app + "@sha256:" + randHex(32), "containerID": "containerd://" + randHex(32),
				"state": map[string]any{"running": map[string]string{"startedAt": ts}}},
			map[string]any{"name": "proxy", "ready": true, "started": true, "restartCount": 0, "image": "registry.example.com/mesh/proxy:v1.24.3",
				"imageID": "registry.example.com/mesh/proxy@sha256:" + randHex(32), "containerID": "containerd://" + randHex(32),
				"state": map[string]any{"running": map[string]string{"startedAt": ts}}},
		},
	}}
	b, _ := json.Marshal(status)
	return c.Patch(ctx, client.Path("v1", "pods", ns, name, "status"), client.MergePatch, map[string][]string{"fieldManager": {"kubelet"}}, b, nil)
}

func heap() uint64 {
	runtime.GC()
	runtime.GC()
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m.HeapAlloc
}

// smallPod is what a scheduler-like controller needs from a Pod.
type smallPod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod"`
	Spec        struct {
		NodeName string `json:"nodeName,omitempty"`
	} `json:"spec"`
	Status struct {
		Phase string `json:"phase,omitempty"`
	} `json:"status"`
}

type podMeta struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod"`
}

type noop[T any] struct{}

func (noop[T]) Reconcile(context.Context, *T) error { return nil }

func measure(mode, kubeconfig, namespace string) (*result, error) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	if dir := os.Getenv("BENCH_CPUPROFILE_DIR"); dir != "" {
		f, err := os.Create(filepath.Join(dir, mode+".pprof"))
		if err != nil {
			return nil, err
		}
		defer f.Close()
		if err := pprof.StartCPUProfile(f); err != nil {
			return nil, err
		}
		defer pprof.StopCPUProfile()
	}
	before := heap()
	start := time.Now()
	r := &result{Mode: mode}
	switch mode {
	case "client-go", "client-go-strip-managed-fields":
		cfg, err := clientcmd.BuildConfigFromFlags("", kubeconfig)
		if err != nil {
			return nil, err
		}
		cs, err := kubernetes.NewForConfig(cfg)
		if err != nil {
			return nil, err
		}
		f := informers.NewSharedInformerFactoryWithOptions(cs, 0, informers.WithNamespace(namespace))
		inf := f.Core().V1().Pods().Informer()
		if mode == "client-go-strip-managed-fields" {
			if err := inf.SetTransform(crcache.TransformStripManagedFields()); err != nil {
				return nil, err
			}
		}
		f.Start(ctx.Done())
		if !cache.WaitForCacheSync(ctx.Done(), inf.HasSynced) {
			return nil, fmt.Errorf("client-go cache didn't sync")
		}
		r.Sync = time.Since(start).Seconds()
		r.Objects = len(inf.GetStore().List())
		r.Heap = heap() - before
		runtime.KeepAlive(f)
		runtime.KeepAlive(inf)
	default:
		ln, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			return nil, err
		}
		addr := ln.Addr().String()
		ln.Close()
		m := &kube.Manager{Kubeconfig: kubeconfig, Namespace: namespace, Addr: addr, DisableInterning: strings.HasSuffix(mode, "no-interning"),
			DisableStreamingLists: strings.HasSuffix(mode, "paginated"),
			Logger:                slog.New(slog.NewTextHandler(io.Discard, nil))}
		var c kube.Controller
		switch mode {
		case "kube-k8s.Pod", "kube-k8s.Pod-paginated", "kube-k8s.Pod-no-interning":
			c = kube.For[k8s.Pod](noop[k8s.Pod]{}, kube.Named("bench"), kube.Workers(1), kube.Resync(0))
		case "kube-small-projection":
			c = kube.For[smallPod](noop[smallPod]{}, kube.Named("bench"), kube.Workers(1), kube.Resync(0))
		case "kube-metadata-only":
			c = kube.For[podMeta](noop[podMeta]{}, kube.Named("bench"), kube.Workers(1), kube.Resync(0))
		default:
			return nil, fmt.Errorf("unknown mode %q", mode)
		}
		go func() { _ = m.Run(ctx, c) }()
		for {
			if resp, err := http.Get("http://" + addr + "/readyz"); err == nil {
				resp.Body.Close()
				if resp.StatusCode == http.StatusOK {
					break
				}
			}
			time.Sleep(20 * time.Millisecond)
		}
		r.Sync = time.Since(start).Seconds()
		// Let the controller finish reconciling so its queue is empty.
		time.Sleep(2 * time.Second)
		r.Heap = heap() - before
		objects, err := cacheObjects(addr)
		if err != nil {
			return nil, err
		}
		r.Objects = objects
	}
	return r, nil
}

// cacheObjects sums the kube_cache_objects gauge from a manager's metrics.
func cacheObjects(addr string) (int, error) {
	resp, err := http.Get("http://" + addr + "/metrics")
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		return 0, err
	}
	total := 0
	for line := range strings.Lines(string(b)) {
		if !strings.HasPrefix(line, "kube_cache_objects{") {
			continue
		}
		var n int
		fields := strings.Fields(line)
		_, _ = fmt.Sscan(fields[len(fields)-1], &n)
		total += n
	}
	return total, nil
}
