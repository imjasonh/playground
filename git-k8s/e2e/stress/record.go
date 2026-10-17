package main

import (
	"bufio"
	"cmp"
	"context"
	"encoding/json"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

// rec is one line of a run's log.
type rec struct {
	T    time.Time       `json:"t"`
	Kind string          `json:"kind"`
	D    json.RawMessage `json:"d"`
}

// recorder appends records to log.jsonl in a run's directory.
type recorder struct {
	mu  sync.Mutex
	f   *os.File
	w   *bufio.Writer
	enc *json.Encoder
}

func newRecorder(path string) (*recorder, error) {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0o644)
	if err != nil {
		return nil, err
	}
	w := bufio.NewWriterSize(f, 1<<20)
	return &recorder{f: f, w: w, enc: json.NewEncoder(w)}, nil
}

func (r *recorder) add(kind string, at time.Time, d any) {
	b, err := json.Marshal(d)
	if err != nil {
		logf("encoding a %s record: %v", kind, err)
		return
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	_ = r.enc.Encode(rec{T: at.UTC(), Kind: kind, D: b})
}

func (r *recorder) flush() {
	r.mu.Lock()
	defer r.mu.Unlock()
	_ = r.w.Flush()
}

func (r *recorder) close() {
	r.flush()
	_ = r.f.Close()
}

// The types that follow are the parts of API objects that the harness
// reads, and the records that it writes for them.

type checkResult struct {
	Commit       string            `json:"commit,omitempty"`
	ParentCommit string            `json:"parentCommit,omitempty"`
	MergeBase    string            `json:"mergeBase,omitempty"`
	State        string            `json:"state,omitempty"`
	Message      string            `json:"message,omitempty"`
	Outputs      map[string]string `json:"outputs,omitempty"`
	FilesOnly    bool              `json:"filesOnly,omitempty"`
}

type queuedStatus struct {
	Since    time.Time `json:"since"`
	Head     string    `json:"head,omitempty"`
	Position int       `json:"position,omitempty"`
}

type condition struct {
	Type               string    `json:"type"`
	Status             string    `json:"status"`
	Reason             string    `json:"reason,omitempty"`
	Message            string    `json:"message,omitempty"`
	ObservedGeneration int64     `json:"observedGeneration,omitempty"`
	LastTransitionTime time.Time `json:"lastTransitionTime,omitzero"`
}

type objectMeta struct {
	Name              string            `json:"name"`
	Namespace         string            `json:"namespace"`
	UID               string            `json:"uid"`
	Generation        int64             `json:"generation"`
	Labels            map[string]string `json:"labels"`
	Annotations       map[string]string `json:"annotations"`
	DeletionTimestamp *time.Time        `json:"deletionTimestamp"`
	CreationTimestamp time.Time         `json:"creationTimestamp"`
	OwnerReferences   []struct {
		Kind string `json:"kind"`
		Name string `json:"name"`
	} `json:"ownerReferences"`
}

type branchObject struct {
	Metadata objectMeta `json:"metadata"`
	Spec     struct {
		Repository string `json:"repository"`
		Branch     string `json:"branch"`
		Head       string `json:"head"`
		Parent     string `json:"parent"`
		ParentHead string `json:"parentHead"`
	} `json:"spec"`
	Status struct {
		Checks     map[string]checkResult `json:"checks"`
		State      string                 `json:"state"`
		Queued     *queuedStatus          `json:"queued"`
		Queue      []string               `json:"queue"`
		Conditions []condition            `json:"conditions"`
		Diverged   json.RawMessage        `json:"diverged"`
	} `json:"status"`
}

const (
	approveAnnotation    = "git-k8s.imjasonh.com/approve"
	approvedByAnnotation = "git-k8s.imjasonh.com/approved-by"
)

// branchRec is a Branch object as one watch event showed it.
type branchRec struct {
	Type       string                 `json:"type"`
	NS         string                 `json:"ns"`
	Name       string                 `json:"name"`
	Repo       string                 `json:"repo"`
	Branch     string                 `json:"branch"`
	Gen        int64                  `json:"gen"`
	Head       string                 `json:"head"`
	Parent     string                 `json:"parent,omitempty"`
	ParentHead string                 `json:"parentHead,omitempty"`
	State      string                 `json:"state,omitempty"`
	Landed     *condition             `json:"landed,omitempty"`
	Queued     *queuedStatus          `json:"queued,omitempty"`
	Queue      []string               `json:"queue,omitempty"`
	Checks     map[string]checkResult `json:"checks,omitempty"`
	Diverged   json.RawMessage        `json:"diverged,omitempty"`
	Approve    string                 `json:"approve,omitempty"`
	ApprovedBy string                 `json:"approvedBy,omitempty"`
	Deleting   bool                   `json:"deleting,omitempty"`
}

func toBranchRec(typ string, b *branchObject) *branchRec {
	r := &branchRec{
		Type: typ, NS: b.Metadata.Namespace, Name: b.Metadata.Name, Repo: b.Spec.Repository, Branch: b.Spec.Branch,
		Gen: b.Metadata.Generation, Head: b.Spec.Head, Parent: b.Spec.Parent, ParentHead: b.Spec.ParentHead,
		State: b.Status.State, Queued: b.Status.Queued, Queue: b.Status.Queue, Checks: b.Status.Checks,
		Approve: b.Metadata.Annotations[approveAnnotation], ApprovedBy: b.Metadata.Annotations[approvedByAnnotation],
		Deleting: b.Metadata.DeletionTimestamp != nil,
	}
	if string(b.Status.Diverged) != "null" {
		r.Diverged = b.Status.Diverged
	}
	for i := range b.Status.Conditions {
		if c := b.Status.Conditions[i]; c.Type == "Landed" {
			r.Landed = &c
		}
	}
	for name, c := range r.Checks {
		if len(c.Message) > 300 {
			c.Message = c.Message[:300] + "..."
			r.Checks[name] = c
		}
	}
	return r
}

type event struct {
	Metadata            objectMeta `json:"metadata"`
	EventTime           *time.Time `json:"eventTime"`
	Reason              string     `json:"reason"`
	Note                string     `json:"note"`
	Type                string     `json:"type"`
	ReportingController string     `json:"reportingController"`
	Action              string     `json:"action"`
	Regarding           struct {
		Kind string `json:"kind"`
		Name string `json:"name"`
	} `json:"regarding"`
	Series *struct {
		Count            int       `json:"count"`
		LastObservedTime time.Time `json:"lastObservedTime"`
	} `json:"series"`
	DeprecatedFirstTimestamp *time.Time `json:"deprecatedFirstTimestamp"`
}

type eventRec struct {
	Type       string    `json:"type"`
	NS         string    `json:"ns"`
	Name       string    `json:"name"`
	EventTime  time.Time `json:"eventTime,omitzero"`
	Reason     string    `json:"reason"`
	Note       string    `json:"note"`
	EvType     string    `json:"evType"`
	Controller string    `json:"controller,omitempty"`
	Action     string    `json:"action,omitempty"`
	Kind       string    `json:"regardingKind"`
	Object     string    `json:"regardingName"`
	Count      int       `json:"count,omitempty"`
	Last       time.Time `json:"last,omitzero"`
}

type pod struct {
	Metadata objectMeta `json:"metadata"`
	Status   struct {
		Phase                 string            `json:"phase"`
		InitContainerStatuses []containerStatus `json:"initContainerStatuses"`
		ContainerStatuses     []containerStatus `json:"containerStatuses"`
	} `json:"status"`
}

type containerStatus struct {
	Name         string `json:"name"`
	RestartCount int    `json:"restartCount"`
	State        struct {
		Waiting *struct {
			Reason string `json:"reason"`
		} `json:"waiting"`
		Running *struct {
			StartedAt time.Time `json:"startedAt"`
		} `json:"running"`
		Terminated *struct {
			Reason     string    `json:"reason"`
			ExitCode   int       `json:"exitCode"`
			StartedAt  time.Time `json:"startedAt"`
			FinishedAt time.Time `json:"finishedAt"`
		} `json:"terminated"`
	} `json:"state"`
}

type containerRec struct {
	Name     string    `json:"name"`
	State    string    `json:"state"`
	Started  time.Time `json:"started,omitzero"`
	Finished time.Time `json:"finished,omitzero"`
	Restarts int       `json:"restarts,omitempty"`
}

func toContainerRecs(statuses []containerStatus) []containerRec {
	var out []containerRec
	for _, s := range statuses {
		c := containerRec{Name: s.Name, Restarts: s.RestartCount}
		switch {
		case s.State.Terminated != nil:
			t := s.State.Terminated
			c.State = "terminated:" + t.Reason + ":" + strconv.Itoa(t.ExitCode)
			c.Started, c.Finished = t.StartedAt, t.FinishedAt
		case s.State.Running != nil:
			c.State, c.Started = "running", s.State.Running.StartedAt
		case s.State.Waiting != nil:
			c.State = "waiting:" + s.State.Waiting.Reason
		}
		out = append(out, c)
	}
	return out
}

type podRec struct {
	Type     string         `json:"type"`
	NS       string         `json:"ns"`
	Name     string         `json:"name"`
	UID      string         `json:"uid"`
	App      string         `json:"app,omitempty"`
	Owner    string         `json:"owner,omitempty"`
	Phase    string         `json:"phase,omitempty"`
	Deleting bool           `json:"deleting,omitempty"`
	Init     []containerRec `json:"init,omitempty"`
	Main     []containerRec `json:"main,omitempty"`
}

func isTestPod(m *objectMeta) bool {
	return m.Labels["app.kubernetes.io/name"] == "check-gotest" && m.Labels["app.kubernetes.io/component"] == "test"
}

// cpuRec is the CPU that the kind node used in the last interval, in
// cores, with a breakdown by group of Pods.
type cpuRec struct {
	Node   float64            `json:"node"`
	Host   float64            `json:"host"`
	MemMiB float64            `json:"memMiB"`
	Groups map[string]float64 `json:"groups"`
}

type metricsRec struct {
	Program string             `json:"program"`
	Pod     string             `json:"pod"`
	Samples map[string]float64 `json:"samples"`
}

type extRec struct {
	Repo string `json:"repo"`
	Ref  string `json:"ref"`
	SHA  string `json:"sha"`
}

type tickParent struct {
	Queue int    `json:"queue"`
	Head  string `json:"head,omitempty"`
	Ext   string `json:"ext,omitempty"`
}

type tickBranch struct {
	Repo   string `json:"repo"`
	Branch string `json:"branch"`
	Head   string `json:"head"`
	State  string `json:"state,omitempty"`
	Pos    int    `json:"pos,omitempty"`
	Checks string `json:"checks"`
}

type tickRec struct {
	Parents  map[string]tickParent `json:"parents"`
	Branches []tickBranch          `json:"branches"`
	Pods     int                   `json:"testPods"`
}

// world is what the watchers last saw. Its methods are safe for
// concurrent use.
type world struct {
	mu       sync.Mutex
	prefix   string
	branches map[string]*branchRec // by namespace/name
	byBranch map[string]string     // namespace/repository/branch to namespace/name
	events   []eventRec
	pods     map[string]podRec // by the UID in the Pod's cgroup name
	ext      map[string]string // external repository/ref to SHA
	changed  chan struct{}
}

func newWorld(prefix string) *world {
	return &world{
		prefix: prefix, branches: map[string]*branchRec{}, byBranch: map[string]string{},
		pods: map[string]podRec{}, ext: map[string]string{}, changed: make(chan struct{}, 1),
	}
}

func (w *world) notify() {
	select {
	case w.changed <- struct{}{}:
	default:
	}
}

// branch returns the last record of the Branch object for branch in repo, or
// nil if there's none or it was deleted.
func (w *world) branch(ns, repo, branch string) *branchRec {
	w.mu.Lock()
	defer w.mu.Unlock()
	key, ok := w.byBranch[ns+"/"+repo+"/"+branch]
	if !ok {
		return nil
	}
	return w.branches[key]
}

func (w *world) eventsSince(i int) ([]eventRec, int) {
	w.mu.Lock()
	defer w.mu.Unlock()
	return slices.Clone(w.events[i:]), len(w.events)
}

func (w *world) extRef(repo, ref string) string {
	w.mu.Lock()
	defer w.mu.Unlock()
	return w.ext[repo+"/"+ref]
}

// startWatchers records Branch objects, Events, and Pods in namespaces that
// start with w.prefix, and the uids of all Pods for the CPU sampler.
func startWatchers(ctx context.Context, k *kubeClient, r *recorder, w *world) {
	go k.watch(ctx, "/apis/git-k8s.imjasonh.com/v1alpha1/branches", func(typ string, raw json.RawMessage, at time.Time) {
		var b branchObject
		if err := json.Unmarshal(raw, &b); err != nil || !strings.HasPrefix(b.Metadata.Namespace, w.prefix) {
			return
		}
		br := toBranchRec(typ, &b)
		key := br.NS + "/" + br.Name
		w.mu.Lock()
		old := w.branches[key]
		same := old != nil && typ != "DELETED" && sameBranch(old, br)
		if typ == "DELETED" {
			delete(w.branches, key)
			if w.byBranch[br.NS+"/"+br.Repo+"/"+br.Branch] == key {
				delete(w.byBranch, br.NS+"/"+br.Repo+"/"+br.Branch)
			}
		} else {
			w.branches[key] = br
			w.byBranch[br.NS+"/"+br.Repo+"/"+br.Branch] = key
		}
		w.mu.Unlock()
		if !same {
			r.add("branch", at, br)
			w.notify()
		}
	})
	go k.watch(ctx, "/apis/events.k8s.io/v1/events", func(typ string, raw json.RawMessage, at time.Time) {
		var e event
		if err := json.Unmarshal(raw, &e); err != nil || !strings.HasPrefix(e.Metadata.Namespace, w.prefix) || typ == "DELETED" {
			return
		}
		er := eventRec{
			Type: typ, NS: e.Metadata.Namespace, Name: e.Metadata.Name, Reason: e.Reason, Note: e.Note, EvType: e.Type,
			Controller: e.ReportingController, Action: e.Action, Kind: e.Regarding.Kind, Object: e.Regarding.Name,
		}
		switch {
		case e.EventTime != nil:
			er.EventTime = *e.EventTime
		case e.DeprecatedFirstTimestamp != nil:
			er.EventTime = *e.DeprecatedFirstTimestamp
		}
		if e.Series != nil {
			er.Count, er.Last = e.Series.Count, e.Series.LastObservedTime
		}
		w.mu.Lock()
		w.events = append(w.events, er)
		w.mu.Unlock()
		r.add("event", at, er)
		w.notify()
	})
	go k.watch(ctx, "/api/v1/pods", func(typ string, raw json.RawMessage, at time.Time) {
		var p pod
		if err := json.Unmarshal(raw, &p); err != nil {
			return
		}
		pr := podRec{
			Type: typ, NS: p.Metadata.Namespace, Name: p.Metadata.Name, UID: p.Metadata.UID,
			App: p.Metadata.Labels["app.kubernetes.io/name"], Phase: p.Status.Phase, Deleting: p.Metadata.DeletionTimestamp != nil,
		}
		test := isTestPod(&p.Metadata)
		if test {
			pr.App = "test"
			for _, o := range p.Metadata.OwnerReferences {
				if o.Kind == "Branch" {
					pr.Owner = o.Name
				}
			}
			pr.Init = toContainerRecs(p.Status.InitContainerStatuses)
		}
		pr.Main = toContainerRecs(p.Status.ContainerStatuses)
		// w.pods has each Pod by its cgroup's UID. A static Pod's cgroup
		// has the kubelet's UID for it, which is its mirror Pod's
		// kubernetes.io/config.hash annotation, not the mirror Pod's UID.
		key := cmp.Or(p.Metadata.Annotations["kubernetes.io/config.hash"], pr.UID)
		w.mu.Lock()
		old, seen := w.pods[key]
		if typ == "DELETED" {
			delete(w.pods, key)
		} else {
			w.pods[key] = pr
		}
		w.mu.Unlock()
		// Record every change to a test Pod in a scenario's namespace, and
		// when other Pods start, stop, or restart.
		if test && strings.HasPrefix(pr.NS, w.prefix) {
			if !seen || typ == "DELETED" || !samePod(old, pr) {
				r.add("pod", at, pr)
			}
		} else if !seen || typ == "DELETED" || restarts(old) != restarts(pr) || old.Phase != pr.Phase {
			r.add("pod", at, podRec{Type: typ, NS: pr.NS, Name: pr.Name, UID: pr.UID, App: pr.App, Phase: pr.Phase, Main: pr.Main})
		}
	})
}

// sameBranch reports whether two records differ only in their watch event
// types.
func sameBranch(a, b *branchRec) bool {
	x, y := *a, *b
	x.Type, y.Type = "", ""
	xb, _ := json.Marshal(x)
	yb, _ := json.Marshal(y)
	return string(xb) == string(yb)
}

func samePod(a, b podRec) bool {
	a.Type, b.Type = "", ""
	x, _ := json.Marshal(a)
	y, _ := json.Marshal(b)
	return string(x) == string(y)
}

func restarts(p podRec) int {
	n := 0
	for _, c := range p.Main {
		n += c.Restarts
	}
	return n
}

// podGroup names the group whose CPU a Pod counts toward.
func podGroup(p podRec) string {
	switch {
	case p.App == "test":
		return "test-pods"
	case p.NS == "kube-system":
		for _, prefix := range []string{"kube-apiserver", "etcd", "kube-controller-manager", "kube-scheduler"} {
			if strings.HasPrefix(p.Name, prefix) {
				return prefix
			}
		}
		return "kube-system-other"
	case p.NS == "git-k8s" || strings.HasPrefix(p.NS, "check-") || p.NS == "go-cache":
		return p.NS
	}
	return "other-pods"
}

var podSlice = regexp.MustCompile(`-pod([0-9a-f_]+)\.slice$`)

// sampleCPU records the CPU and memory of the kind node's container once a
// second, from its cgroup, with the CPU of each Pod's cgroup grouped by
// podGroup.
func sampleCPU(ctx context.Context, r *recorder, w *world, cgroup string) {
	readUsage := func(dir string) (float64, bool) {
		b, err := os.ReadFile(filepath.Join(dir, "cpu.stat"))
		if err != nil {
			return 0, false
		}
		for line := range strings.SplitSeq(string(b), "\n") {
			if v, ok := strings.CutPrefix(line, "usage_usec "); ok {
				n, err := strconv.ParseFloat(v, 64)
				return n, err == nil
			}
		}
		return 0, false
	}
	readHost := func() (busy, total float64) {
		b, err := os.ReadFile("/proc/stat")
		if err != nil {
			return 0, 0
		}
		fields := strings.Fields(strings.SplitN(string(b), "\n", 2)[0])
		for i, f := range fields[1:] {
			v, _ := strconv.ParseFloat(f, 64)
			total += v
			if i != 3 && i != 4 {
				busy += v
			}
		}
		return busy, total
	}
	ncpu := float64(numCPU())
	pods := filepath.Join(cgroup, "kubelet.slice", "kubelet-kubepods.slice")
	// podUsage returns the CPU that each Pod's cgroup counted, by the UID in
	// the cgroup's name. Pod cgroups are at most two levels below
	// kubelet-kubepods.slice, under a QoS class's slice or not.
	podUsage := func() map[string]float64 {
		var dirs []string
		level1, _ := os.ReadDir(pods)
		for _, d := range level1 {
			if !d.IsDir() {
				continue
			}
			p := filepath.Join(pods, d.Name())
			dirs = append(dirs, p)
			level2, _ := os.ReadDir(p)
			for _, d2 := range level2 {
				if d2.IsDir() {
					dirs = append(dirs, filepath.Join(p, d2.Name()))
				}
			}
		}
		usage := map[string]float64{}
		for _, dir := range dirs {
			m := podSlice.FindStringSubmatch(dir)
			if m == nil {
				continue
			}
			if u, ok := readUsage(dir); ok {
				usage[strings.ReplaceAll(m[1], "_", "-")] = u
			}
		}
		return usage
	}
	lastNode, _ := readUsage(cgroup)
	lastPods := podUsage()
	lastBusy, lastTotal := readHost()
	last := time.Now()
	t := time.NewTicker(time.Second)
	defer t.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
		now := time.Now()
		elapsed := float64(now.Sub(last).Microseconds())
		last = now
		node, ok := readUsage(cgroup)
		if !ok {
			continue
		}
		rec := cpuRec{Node: (node - lastNode) / elapsed, Groups: map[string]float64{}}
		lastNode = node
		busy, total := readHost()
		if total > lastTotal {
			rec.Host = (busy - lastBusy) / (total - lastTotal) * ncpu
		}
		lastBusy, lastTotal = busy, total
		if b, err := os.ReadFile(filepath.Join(cgroup, "memory.current")); err == nil {
			v, _ := strconv.ParseFloat(strings.TrimSpace(string(b)), 64)
			rec.MemMiB = v / (1 << 20)
		}
		current := podUsage()
		w.mu.Lock()
		var attributed float64
		for uid, usage := range current {
			// A Pod that started during the interval used everything that
			// its cgroup counted, and lastPods doesn't have it.
			prev := lastPods[uid]
			group := "unknown-pods"
			if p, ok := w.pods[uid]; ok {
				group = podGroup(p)
			}
			d := (usage - prev) / elapsed
			rec.Groups[group] += d
			attributed += d
		}
		w.mu.Unlock()
		lastPods = current
		rec.Groups["node-other"] = max(0, rec.Node-attributed)
		for g, v := range rec.Groups {
			rec.Groups[g] = round3(v)
		}
		rec.Node, rec.Host, rec.MemMiB = round3(rec.Node), round3(rec.Host), round3(rec.MemMiB)
		r.add("cpu", now, rec)
	}
}

func round3(v float64) float64 {
	return float64(int64(v*1000+0.5)) / 1000
}

// programs are the Deployments whose metrics the harness scrapes, by
// namespace, which is also the program's name.
var programs = []string{"git-k8s", "check-base", "check-gofmt", "check-risk", "check-approval", "check-gotest", "go-cache"}

// scrapeMetrics records the kube_ and go_cache_ metrics of every Pod of
// programs every interval.
func scrapeMetrics(ctx context.Context, k *kubeClient, r *recorder, interval time.Duration) {
	t := time.NewTicker(interval)
	defer t.Stop()
	for {
		scrapeOnce(ctx, k, r)
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
	}
}

func scrapeOnce(ctx context.Context, k *kubeClient, r *recorder) {
	for _, program := range programs {
		var list struct {
			Items []pod `json:"items"`
		}
		if err := k.get(ctx, "/api/v1/namespaces/"+program+"/pods?labelSelector=app.kubernetes.io/name="+program, &list); err != nil {
			continue
		}
		for _, p := range list.Items {
			if p.Status.Phase != "Running" {
				continue
			}
			b, err := k.do(ctx, "GET", "/api/v1/namespaces/"+program+"/pods/"+p.Metadata.Name+":8080/proxy/metrics", "", nil)
			if err != nil {
				continue
			}
			samples := map[string]float64{}
			for line := range strings.SplitSeq(string(b), "\n") {
				if !strings.HasPrefix(line, "kube_") && !strings.HasPrefix(line, "go_cache_") && !strings.HasPrefix(line, "process_") {
					continue
				}
				i := strings.LastIndexByte(line, ' ')
				if i < 0 {
					continue
				}
				v, err := strconv.ParseFloat(line[i+1:], 64)
				if err != nil {
					continue
				}
				samples[line[:i]] = v
			}
			r.add("metrics", time.Now(), metricsRec{Program: program, Pod: p.Metadata.Name, Samples: samples})
		}
	}
}

// pollRefs records changes to refs in the git server's repositories, which
// it reads from disk, every 100ms.
func pollRefs(ctx context.Context, r *recorder, w *world, root string, repos func() []string, refs []string) {
	t := time.NewTicker(100 * time.Millisecond)
	defer t.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
		for _, repo := range repos() {
			for _, ref := range refs {
				sha := readRef(filepath.Join(root, repo+".git"), "refs/heads/"+ref)
				w.mu.Lock()
				old := w.ext[repo+"/"+ref]
				w.ext[repo+"/"+ref] = sha
				w.mu.Unlock()
				if sha != old {
					r.add("ext", time.Now(), extRec{Repo: repo, Ref: ref, SHA: sha})
					w.notify()
				}
			}
		}
	}
}

// readRef reads a ref from a bare repository's loose refs or packed-refs,
// and returns "" if the repository doesn't have it.
func readRef(dir, ref string) string {
	if b, err := os.ReadFile(filepath.Join(dir, ref)); err == nil {
		return strings.TrimSpace(string(b))
	}
	b, err := os.ReadFile(filepath.Join(dir, "packed-refs"))
	if err != nil {
		return ""
	}
	for line := range strings.SplitSeq(string(b), "\n") {
		if sha, name, ok := strings.Cut(line, " "); ok && name == ref {
			return sha
		}
	}
	return ""
}

// tick records a summary of every Branch object in the scenario's namespaces
// once a second: each branch's state, head, check states, and place in the
// queue, and the length of each parent's queue.
func tick(ctx context.Context, r *recorder, w *world) {
	t := time.NewTicker(time.Second)
	defer t.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
		rec := tickRec{Parents: map[string]tickParent{}}
		w.mu.Lock()
		for _, b := range w.branches {
			if b.Parent == "" {
				rec.Parents[b.NS+"/"+b.Repo] = tickParent{Queue: len(b.Queue), Head: short(b.Head), Ext: short(w.ext[repoKey(b.NS, b.Repo)+"/main"])}
				continue
			}
			tb := tickBranch{Repo: b.NS + "/" + b.Repo, Branch: b.Branch, Head: short(b.Head), State: b.State}
			if b.Queued != nil {
				tb.Pos = b.Queued.Position
			}
			tb.Checks = summarizeChecks(b)
			rec.Branches = append(rec.Branches, tb)
		}
		for _, p := range w.pods {
			if p.App == "test" && strings.HasPrefix(p.NS, w.prefix) && (p.Phase == "Pending" || p.Phase == "Running") {
				rec.Pods++
			}
		}
		w.mu.Unlock()
		sort.Slice(rec.Branches, func(i, j int) bool {
			a, b := rec.Branches[i], rec.Branches[j]
			return a.Repo+" "+a.Branch < b.Repo+" "+b.Branch
		})
		r.add("tick", time.Now(), rec)
	}
}

// summarizeChecks writes a branch's check results in one string, such as
// "base:P gofmt:F* gotest:R", where P, F, R, X, and E stand for Passed,
// Failed, Running, Fixed, and Error, * marks a result for an older head or
// parent head, or for the change on top of a merge base other than the
// parent's head, and risk shows its level.
func summarizeChecks(b *branchRec) string {
	names := make([]string, 0, len(b.Checks))
	for name := range b.Checks {
		names = append(names, name)
	}
	sort.Strings(names)
	var parts []string
	for _, name := range names {
		c := b.Checks[name]
		s := name + ":" + abbreviate(c.State)
		if c.Commit != b.Head || (c.ParentCommit != "" && c.ParentCommit != b.ParentHead) || (c.MergeBase != "" && c.MergeBase != b.ParentHead) {
			s += "*"
		}
		if level := c.Outputs["level"]; level != "" {
			s += "(" + level + ")"
		}
		if c.Outputs["behind"] == "true" {
			s += "(behind)"
		}
		parts = append(parts, s)
	}
	return strings.Join(parts, " ")
}

func abbreviate(state string) string {
	switch state {
	case "Passed":
		return "P"
	case "Failed":
		return "F"
	case "Running":
		return "R"
	case "Fixed":
		return "X"
	case "Error":
		return "E"
	case "":
		return "-"
	}
	return state
}

func short(sha string) string {
	if len(sha) > 7 {
		return sha[:7]
	}
	return sha
}
