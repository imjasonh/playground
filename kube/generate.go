//go:build !kube_nogenerate

// The generate command builds the program for its image with the
// kube_nogenerate tag, which leaves this file out, so the program that
// runs in the cluster doesn't carry go-containerregistry.

package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime/debug"
	"slices"
	"strings"

	v1 "github.com/google/go-containerregistry/pkg/v1"

	"github.com/imjasonh/playground/kube/internal/analysis"
	"github.com/imjasonh/playground/kube/internal/image"
	"github.com/imjasonh/playground/kube/internal/yaml"
)

// defaultBase is the image that generate builds on: Chainguard's static
// image, which holds CA certificates and time zone data and runs as a
// non-root user.
const defaultBase = "cgr.dev/chainguard/static:latest"

// scopeVerbs are the RBAC verbs that each function of a reconcile needs
// for its type argument.
var scopeVerbs = map[string][]string{
	"Get":    {"list", "watch"},
	"List":   {"list", "watch"},
	"Fetch":  {"get"},
	"Own":    {"list", "watch", "create", "patch", "delete"},
	"Apply":  {"create", "patch"},
	"Delete": {"delete"},
}

type generateOptions struct {
	// program is the executable's name, which the program uses for itself
	// at run time, and name is the same as a Kubernetes object name.
	program, name string
	registry      string
	base          string
	platforms     []v1.Platform
	namespace     string
	replicas      int
	shards        int
	tag           string
	// tmpSize is the size limit of the volume at /tmp, or empty for none.
	tmpSize string
	// watchNamespace is the one namespace that the program watches, or
	// empty for every namespace.
	watchNamespace string
	// args are more arguments for the program in the Deployment.
	args   []string
	stderr io.Writer
}

// quantity matches the Kubernetes quantities that people write for sizes.
var quantity = regexp.MustCompile(`^[0-9]+(\.[0-9]+)?([eE][0-9]+|Ki|Mi|Gi|Ti|Pi|Ei|k|M|G|T|P|E)?$`)

func (o *generateOptions) logf(format string, args ...any) {
	fmt.Fprintf(o.stderr, format+"\n", args...)
}

// generate implements the generate command. It works out the RBAC rules
// the program needs from its controllers and source, builds the program
// into an image for each platform, pushes the image, and writes the YAML
// that installs it to stdout.
func generate(ctx context.Context, args []string, controllers []Controller, stdout, stderr io.Writer) error {
	o := &generateOptions{program: filepath.Base(os.Args[0]), stderr: stderr}
	o.name = objectName(o.program)
	fs := flag.NewFlagSet(o.program+" generate", flag.ContinueOnError)
	fs.SetOutput(stderr)
	fs.StringVar(&o.registry, "registry", "", "registry, and optionally a repository prefix, to push the image to, such as ghcr.io/you (required)")
	fs.StringVar(&o.base, "base", defaultBase, "base image")
	platforms := fs.String("platform", "linux/amd64,linux/arm64", "comma-separated platforms to build the image for")
	fs.StringVar(&o.namespace, "namespace", o.name, "namespace to install the program in")
	fs.IntVar(&o.replicas, "replicas", 2, "pods to run; more than one turns on leader election")
	fs.IntVar(&o.shards, "shards", 1, "split reconciles across replicas in this many shards")
	fs.StringVar(&o.tag, "tag", "latest", "tag for the image, in addition to its digest")
	fs.StringVar(&o.tmpSize, "tmp-size", "", "size limit of the emptyDir volume at /tmp, such as 1Gi; empty means no limit")
	fs.StringVar(&o.watchNamespace, "watch-namespace", "", "namespace for the program to watch instead of every namespace; the rules for namespaced resources go in a Role there")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: %s generate -registry=REGISTRY [flags] [-- PROGRAM_FLAGS] | kubectl apply -f -\n\n", o.program)
		fmt.Fprintf(stderr, "Builds the program into an image, pushes it to REGISTRY/%s, and writes the YAML that installs it.\n", o.name)
		fmt.Fprintf(stderr, "Flags after -- are passed to the program in the Deployment.\n\n")
		fs.PrintDefaults()
	}
	if i := slices.Index(args, "--"); i >= 0 {
		args, o.args = args[:i], args[i+1:]
	}
	if err := fs.Parse(args); err != nil {
		return err
	}
	switch {
	case fs.NArg() > 0:
		return fmt.Errorf("generate: unexpected argument %q; put the program's own flags after --", fs.Arg(0))
	case o.registry == "":
		fs.Usage()
		return errors.New("generate: -registry is required")
	case o.replicas < 1 || o.shards < 1:
		return errors.New("generate: -replicas and -shards must be at least 1")
	case o.tmpSize != "" && !quantity.MatchString(o.tmpSize):
		return fmt.Errorf("generate: -tmp-size %q isn't a quantity, such as 512Mi or 2Gi", o.tmpSize)
	case o.watchNamespace != "" && objectName(o.watchNamespace) != o.watchNamespace:
		return fmt.Errorf("generate: -watch-namespace %q isn't a namespace name", o.watchNamespace)
	}
	o.registry = strings.TrimSuffix(o.registry, "/")
	for _, s := range strings.Split(*platforms, ",") {
		p, err := v1.ParsePlatform(strings.TrimSpace(s))
		if err != nil || p.OS == "" || p.Architecture == "" {
			return fmt.Errorf("generate: platform %q isn't os/architecture or os/architecture/variant", s)
		}
		o.platforms = append(o.platforms, *p)
	}
	if len(o.platforms) == 0 {
		return errors.New("generate: -platform needs at least one platform")
	}
	bi, ok := debug.ReadBuildInfo()
	if !ok || bi.Path == "" || bi.Path == "command-line-arguments" {
		return errors.New("generate: can't tell which package to build; run go run PACKAGE generate from the program's module")
	}

	p, err := o.plan(ctx, controllers, bi.Path)
	if err != nil {
		return err
	}
	ref, err := o.push(ctx, bi.Path)
	if err != nil {
		return err
	}
	docs := o.manifests(ref, p)
	var out bytes.Buffer
	fmt.Fprintf(&out, "# %s, built by %s generate from %s.\n", ref, o.program, bi.Path)
	for i, d := range docs {
		if i > 0 {
			out.WriteString("---\n")
		}
		b, err := json.Marshal(d)
		if err != nil {
			return err
		}
		y, err := yaml.FromJSON(b)
		if err != nil {
			return err
		}
		out.Write(y)
	}
	_, err = stdout.Write(out.Bytes())
	return err
}

// buildEnv is the environment for building and analyzing the program for
// platform p.
func buildEnv(p v1.Platform) []string {
	env := append(os.Environ(), "CGO_ENABLED=0", "GOOS="+p.OS, "GOARCH="+p.Architecture)
	if p.Architecture == "arm" && p.Variant != "" {
		env = append(env, "GOARM="+strings.TrimPrefix(p.Variant, "v"))
	}
	return env
}

// push builds pkg for each platform and pushes the image. It returns the
// image's reference by digest.
func (o *generateOptions) push(ctx context.Context, pkg string) (string, error) {
	dir, err := os.MkdirTemp("", "kube-generate-")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(dir)
	var exes []image.Executable
	for _, p := range o.platforms {
		out := filepath.Join(dir, strings.ReplaceAll(p.String(), "/", "-"), o.program)
		o.logf("building %s for %s", pkg, p)
		cmd := exec.CommandContext(ctx, "go", "build", "-tags=kube_nogenerate", "-trimpath", "-ldflags=-s -w", "-o", out, pkg) // #nosec G204 -- the go command building the program's own package.
		cmd.Env = buildEnv(p)
		cmd.Stdout, cmd.Stderr = o.stderr, o.stderr
		if err := cmd.Run(); err != nil {
			return "", fmt.Errorf("generate: building %s for %s: %w", pkg, p, err)
		}
		exes = append(exes, image.Executable{Platform: p, File: out})
	}
	repo := o.registry + "/" + o.name
	o.logf("pushing %s on %s to %s", o.name, o.base, repo)
	ref, err := image.Push(ctx, image.Image{
		Base:        o.base,
		Repository:  repo,
		Tag:         o.tag,
		Path:        "/app/" + o.program,
		Executables: exes,
	})
	if err != nil {
		return "", err
	}
	o.logf("pushed %s", ref)
	return ref, nil
}

// grants holds RBAC permissions: verbs for a resource, either on every
// object or on one named object.
type grants map[grantKey]map[string]bool

type grantKey struct {
	group, resource, name string
}

func (g grants) add(group, resource, name string, verbs ...string) {
	k := grantKey{group, resource, name}
	if g[k] == nil {
		g[k] = map[string]bool{}
	}
	for _, v := range verbs {
		g[k][v] = true
	}
}

// rules turns grants into RBAC rules, combining resources of a group that
// need the same verbs.
func (g grants) rules() []any {
	type ruleKey struct{ group, name, verbs string }
	resources := map[ruleKey][]string{}
	for k, verbs := range g {
		rk := ruleKey{k.group, k.name, strings.Join(slices.Sorted(maps.Keys(verbs)), ",")}
		resources[rk] = append(resources[rk], k.resource)
	}
	keys := slices.SortedFunc(maps.Keys(resources), func(a, b ruleKey) int {
		return strings.Compare(a.group+"\x00"+strings.Join(slices.Sorted(slices.Values(resources[a])), ",")+"\x00"+a.name,
			b.group+"\x00"+strings.Join(slices.Sorted(slices.Values(resources[b])), ",")+"\x00"+b.name)
	})
	var out []any
	for _, k := range keys {
		r := object{{"apiGroups", []string{k.group}}, {"resources", slices.Sorted(slices.Values(resources[k]))}}
		if k.name != "" {
			r = append(r, field{"resourceNames", []string{k.name}})
		}
		out = append(out, append(r, field{"verbs", strings.Split(k.verbs, ",")}))
	}
	return out
}

// resourceName returns the API group and resource of a type. Without a
// plural tag option, it guesses a built-in type's resource from its kind
// the way Kubernetes names them.
func resourceName(ti *typeInfo) (string, string) {
	if ti.plural != "" {
		return ti.group, ti.plural
	}
	if k := strings.ToLower(ti.kind); strings.HasSuffix(k, "endpoints") {
		return ti.group, k
	}
	return ti.group, pluralize(ti.kind)
}

// installPlan is what the installation must allow and run.
type installPlan struct {
	// cluster holds cluster-wide permissions, local those in the program's
	// own namespace, and watched those in the namespace that it watches,
	// when it watches one.
	cluster, local, watched grants
	webhooks                bool
	// electLeader is set when replicas must take turns reconciling.
	electLeader bool
}

// grantsFor returns where the permissions for ti's resources go. A program
// that watches one namespace needs a namespaced resource only there.
func (p *installPlan) grantsFor(ti *typeInfo, watching bool) grants {
	if watching && ti.scope == "Namespaced" {
		return p.watched
	}
	return p.cluster
}

// plan works out what the program needs. Controllers declare their types,
// and the program's source shows the types its reconciles and webhooks
// read and write.
func (o *generateOptions) plan(ctx context.Context, controllers []Controller, pkg string) (*installPlan, error) {
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}}
	cluster := p.cluster
	watching := o.watchNamespace != ""
	warned := map[string]bool{}
	grantsFor := func(ti *typeInfo) grants {
		if watching && ti.scope == "" && !warned[ti.apiVersion+"/"+ti.kind] {
			warned[ti.apiVersion+"/"+ti.kind] = true
			o.logf("warning: %s %s doesn't say whether it's namespaced, so its rules stay in the ClusterRole; add scope=Namespaced or scope=Cluster to its kube tag", ti.apiVersion, ti.kind)
		}
		return p.grantsFor(ti, watching)
	}
	var crds []string
	// creates holds the CRDs of types that the program defines and owns,
	// which it creates if they're missing.
	creates := map[string]bool{}
	var patchIfOwns []func()
	owns := false
	for _, c := range controllers {
		d, err := c.describe()
		if err != nil {
			return nil, err
		}
		p.webhooks = p.webhooks || d.webhooks
		if !d.reconciles {
			continue
		}
		p.electLeader = o.replicas > 1 || o.shards > 1
		group, plural := resourceName(d.ti)
		own := grantsFor(d.ti)
		if watching && d.versioned {
			// Migrating stored objects to a new version lists and patches
			// them in every namespace.
			o.logf("%s has more than one version, so its rules stay in the ClusterRole", d.ti.kind)
			own = cluster
		}
		own.add(group, plural, "", "get", "list", "watch")
		owns = owns || len(d.owns) > 0
		switch {
		case d.finalizes || d.versioned:
			own.add(group, plural, "", "patch")
		case d.ti.scope != "Cluster":
			// An owned object in another namespace, or a cluster-scoped
			// one, can't carry an owner reference to a namespaced owner, so
			// the framework adds a finalizer to the owner. The source
			// doesn't show which namespace an owned object goes in, so
			// owning any object counts.
			patchIfOwns = append(patchIfOwns, func() { own.add(group, plural, "", "patch") })
		}
		if d.ti.status != nil {
			own.add(group, plural+"/status", "", "patch")
		}
		// Owner references that block the owner's deletion need this.
		own.add(group, plural+"/finalizers", "", "update")
		if d.ti.custom {
			crds = append(crds, plural+"."+group)
		}
		for _, oti := range d.owns {
			g, r := resourceName(oti)
			grantsFor(oti).add(g, r, "", "list", "watch", "delete")
			if oti.custom {
				creates[r+"."+g] = true
			}
		}
	}
	funcs := slices.Sorted(maps.Keys(scopeVerbs))
	o.logf("finding the types that %s reads and writes", pkg)
	uses, unresolved, err := analysis.Find(ctx, analysis.Config{
		Dir: ".", Env: buildEnv(o.platforms[0]), Pattern: pkg,
		Package: reflect.TypeFor[Object]().PkgPath(), Funcs: funcs, Marker: "Object",
	})
	if err != nil {
		return nil, err
	}
	for _, u := range unresolved {
		o.logf("warning: %s: can't tell which types this call passes to kube.%s; add its permissions to the ClusterRole yourself", u.Pos, u.Func)
		owns = owns || u.Func == "Own"
	}
	for _, u := range uses {
		ti := &typeInfo{}
		if err := ti.parseTag(u.Type, u.Name, reflect.StructTag(u.Tag).Get("kube")); err != nil {
			return nil, err
		}
		g, r := resourceName(ti)
		grantsFor(ti).add(g, r, "", scopeVerbs[u.Func]...)
		if u.Func == "Apply" && slices.Contains(u.Fields, "status") {
			grantsFor(ti).add(g, r+"/status", "", "patch")
		}
		if ti.custom && u.Func == "Own" {
			creates[r+"."+g] = true
		}
	}
	if owns || slices.ContainsFunc(uses, func(u analysis.Use) bool { return u.Func == "Own" }) {
		for _, grant := range patchIfOwns {
			grant()
		}
	}
	for _, crd := range crds {
		cluster.add("apiextensions.k8s.io", "customresourcedefinitions", "", "create")
		cluster.add("apiextensions.k8s.io", "customresourcedefinitions", crd, "get", "patch")
		cluster.add("apiextensions.k8s.io", "customresourcedefinitions/status", crd, "patch")
		delete(creates, crd)
	}
	for crd := range creates {
		cluster.add("apiextensions.k8s.io", "customresourcedefinitions", "", "create")
		cluster.add("apiextensions.k8s.io", "customresourcedefinitions", crd, "get")
	}
	// The program deletes webhook configurations that an earlier version
	// of it left, even when it has no webhooks itself.
	config := labelValue(o.program)
	for _, r := range []string{"validatingwebhookconfigurations", "mutatingwebhookconfigurations"} {
		cluster.add("admissionregistration.k8s.io", r, config, "get", "delete")
		if p.webhooks {
			cluster.add("admissionregistration.k8s.io", r, "", "create")
			cluster.add("admissionregistration.k8s.io", r, config, "patch")
		}
	}
	if p.webhooks {
		p.local.add("", "secrets", "", "create")
		p.local.add("", "secrets", config+"-webhook-tls", "get", "update")
	}
	if p.electLeader {
		p.local.add("coordination.k8s.io", "leases", "", "get", "list", "create", "update", "delete")
	}
	if o.watchNamespace == o.namespace {
		for k, verbs := range p.watched {
			for v := range verbs {
				p.local.add(k.group, k.resource, k.name, v)
			}
		}
		clear(p.watched)
	}
	return p, nil
}

// manifests returns the objects that install the program.
func (o *generateOptions) manifests(ref string, p *installPlan) []object {
	labels := map[string]string{"app.kubernetes.io/name": o.name}
	meta := func(name string, namespaced bool) object {
		m := object{{"name", name}}
		if namespaced {
			m = append(m, field{"namespace", o.namespace})
		}
		return append(m, field{"labels", labels})
	}
	subjects := []any{object{{"kind", "ServiceAccount"}, {"name", o.name}, {"namespace", o.namespace}}}
	docs := []object{
		{{"apiVersion", "v1"}, {"kind", "Namespace"}, {"metadata", meta(o.namespace, false)}},
		{{"apiVersion", "v1"}, {"kind", "ServiceAccount"}, {"metadata", meta(o.name, true)}},
		{{"apiVersion", "rbac.authorization.k8s.io/v1"}, {"kind", "ClusterRole"}, {"metadata", meta(o.name, false)}, {"rules", p.cluster.rules()}},
		{
			{"apiVersion", "rbac.authorization.k8s.io/v1"}, {"kind", "ClusterRoleBinding"}, {"metadata", meta(o.name, false)},
			{"roleRef", object{{"apiGroup", "rbac.authorization.k8s.io"}, {"kind", "ClusterRole"}, {"name", o.name}}},
			{"subjects", subjects},
		},
	}
	role := func(m object, g grants) []object {
		return []object{
			{{"apiVersion", "rbac.authorization.k8s.io/v1"}, {"kind", "Role"}, {"metadata", m}, {"rules", g.rules()}},
			{
				{"apiVersion", "rbac.authorization.k8s.io/v1"}, {"kind", "RoleBinding"}, {"metadata", m},
				{"roleRef", object{{"apiGroup", "rbac.authorization.k8s.io"}, {"kind", "Role"}, {"name", o.name}}},
				{"subjects", subjects},
			},
		}
	}
	if len(p.local) > 0 {
		docs = append(docs, role(meta(o.name, true), p.local)...)
	}
	if len(p.watched) > 0 {
		docs = append(docs, role(object{{"name", o.name}, {"namespace", o.watchNamespace}, {"labels", labels}}, p.watched)...)
	}
	args := []string{"-addr=:8080"}
	switch {
	case p.electLeader && o.shards > 1:
		args = append(args, fmt.Sprintf("-shards=%d", o.shards))
	case p.electLeader:
		args = append(args, "-leader-elect")
	}
	if o.watchNamespace != "" {
		args = append(args, "-namespace="+o.watchNamespace)
	}
	ports := []any{object{{"name", "http"}, {"containerPort", 8080}}}
	if p.webhooks {
		args = append(args, "-webhook-addr=:9443", "-webhook-service="+o.namespace+"/"+o.name)
		ports = append(ports, object{{"name", "webhook"}, {"containerPort", 9443}})
		docs = append(docs, object{
			{"apiVersion", "v1"}, {"kind", "Service"}, {"metadata", meta(o.name, true)},
			{"spec", object{
				{"selector", labels},
				{"ports", []any{object{{"name", "webhook"}, {"port", 443}, {"targetPort", "webhook"}}}},
			}},
		})
	}
	args = append(args, o.args...)
	probe := func(path string) object {
		return object{{"httpGet", object{{"path", path}, {"port", "http"}}}}
	}
	container := object{
		{"name", o.name},
		{"image", ref},
		{"args", args},
		{"ports", ports},
		{"readinessProbe", probe("/readyz")},
		{"livenessProbe", probe("/healthz")},
		{"resources", object{{"requests", object{{"cpu", "50m"}, {"memory", "64Mi"}}}}},
		{"securityContext", object{
			{"allowPrivilegeEscalation", false},
			{"readOnlyRootFilesystem", true},
			{"capabilities", object{{"drop", []string{"ALL"}}}},
		}},
		// The root file system is read-only, so give os.TempDir somewhere to
		// write.
		{"volumeMounts", []any{object{{"name", "tmp"}, {"mountPath", "/tmp"}}}},
	}
	tmp := object{}
	if o.tmpSize != "" {
		tmp = object{{"sizeLimit", o.tmpSize}}
	}
	docs = append(docs, object{
		{"apiVersion", "apps/v1"}, {"kind", "Deployment"}, {"metadata", meta(o.name, true)},
		{"spec", object{
			{"replicas", o.replicas},
			{"selector", object{{"matchLabels", labels}}},
			{"template", object{
				{"metadata", object{{"labels", labels}}},
				{"spec", object{
					{"serviceAccountName", o.name},
					{"securityContext", object{{"runAsNonRoot", true}, {"seccompProfile", object{{"type", "RuntimeDefault"}}}}},
					{"containers", []any{container}},
					{"volumes", []any{object{{"name", "tmp"}, {"emptyDir", tmp}}}},
				}},
			}},
		}},
	})
	if o.replicas > 1 {
		docs = append(docs, object{
			{"apiVersion", "policy/v1"}, {"kind", "PodDisruptionBudget"}, {"metadata", meta(o.name, true)},
			{"spec", object{{"maxUnavailable", 1}, {"selector", object{{"matchLabels", labels}}}}},
		})
	}
	return docs
}

// objectName makes s a valid name for a Namespace, Service, or other
// Kubernetes object: lowercase letters, digits, and '-'.
func objectName(s string) string {
	s = strings.Map(func(r rune) rune {
		switch {
		case r >= 'a' && r <= 'z', r >= '0' && r <= '9':
			return r
		case r >= 'A' && r <= 'Z':
			return r + 'a' - 'A'
		}
		return '-'
	}, s)
	if len(s) > 63 {
		s = s[:63]
	}
	if s = strings.Trim(s, "-"); s == "" {
		return "controller"
	}
	return s
}

// object is a JSON object with its keys in order, so the YAML reads like a
// hand-written manifest.
type object []field

type field struct {
	key   string
	value any
}

func (o object) MarshalJSON() ([]byte, error) {
	var b bytes.Buffer
	b.WriteByte('{')
	for i, f := range o {
		if i > 0 {
			b.WriteByte(',')
		}
		k, err := json.Marshal(f.key)
		if err != nil {
			return nil, err
		}
		v, err := json.Marshal(f.value)
		if err != nil {
			return nil, err
		}
		b.Write(k)
		b.WriteByte(':')
		b.Write(v)
	}
	b.WriteByte('}')
	return b.Bytes(), nil
}
