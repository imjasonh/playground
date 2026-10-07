package main

import (
	"flag"
	"maps"
	"net/netip"
	"slices"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

func TestTestPodsPolicy(t *testing.T) {
	defer func(ml, gl, dl labels, dc cidrs, mns, gns, dns, proxy string) {
		mirrorLabels, goCacheLabels, dnsLabels, dnsCIDRs, *mirrorNS, *goCacheNS, *dnsNS, *goProxy = ml, gl, dl, dc, mns, gns, dns, proxy
	}(mirrorLabels, goCacheLabels, dnsLabels, dnsCIDRs, *mirrorNS, *goCacheNS, *dnsNS, *goProxy)
	set := func(name, value string) {
		t.Helper()
		if err := flag.Set(name, value); err != nil {
			t.Fatal(err)
		}
	}
	type conn struct {
		to       dest
		protocol string
		port     int32
		want     bool
	}
	repo := &gitk8s.TrackedRepository{Object: kube.Meta("app", nil)}
	repo.Namespace = "default"
	check := func(conns ...conn) {
		t.Helper()
		policy := testPodsPolicy(repo)
		for _, c := range conns {
			if got := allows(policy.Spec.Egress, c.to, c.protocol, c.port); got != c.want {
				t.Errorf("the policy lets a test Pod reach %s %d on %+v: %v, want %v", c.protocol, c.port, c.to, got, c.want)
			}
		}
	}

	policy := testPodsPolicy(repo)
	if policy.Name != "app-test-pods" || policy.Namespace != "" {
		t.Errorf("policy %s/%s, want app-test-pods in the repository's namespace, which kube.Own defaults to", policy.Namespace, policy.Name)
	}
	if want := map[string]string{"kube.imjasonh.github.io/controller": "check-gotest"}; !maps.Equal(policy.Spec.PodSelector.MatchLabels, want) {
		t.Errorf("the policy selects %v, want check-gotest's Pods, %v", policy.Spec.PodSelector.MatchLabels, want)
	}
	if !slices.Equal(policy.Spec.PolicyTypes, []string{"Ingress", "Egress"}) {
		t.Errorf("policy types = %v; with no ingress rules, Ingress keeps everything from reaching the Pods", policy.Spec.PolicyTypes)
	}

	mirror := dest{ns: "git-k8s", labels: map[string]string{"app.kubernetes.io/name": "git-k8s"}, ip: "10.244.0.5"}
	gofmt := dest{ns: "git-k8s", labels: map[string]string{"app.kubernetes.io/name": "check-gofmt"}, ip: "10.244.0.6"}
	notMirror := dest{ns: "default", labels: map[string]string{"app.kubernetes.io/name": "git-k8s"}, ip: "10.244.1.7"}
	coreDNS := dest{ns: "kube-system", labels: map[string]string{"k8s-app": "kube-dns", "pod-template-hash": "668d6bf9bc"}, ip: "10.244.0.2"}
	apiServer := dest{ns: "kube-system", labels: map[string]string{"component": "kube-apiserver"}, ip: "172.18.0.2"}
	publicDNS := dest{ip: "8.8.8.8"}
	public := dest{ip: "203.0.113.10"}
	metadata := dest{ip: "169.254.169.254"}
	node := dest{ip: "172.18.0.3"}
	cgnat := dest{ip: "100.64.0.1"}
	home := dest{ip: "192.168.1.1"}
	nodeLocalDNS := dest{ip: "169.254.20.10"}
	goCache := dest{ns: "go-cache", labels: map[string]string{"app.kubernetes.io/name": "go-cache"}, ip: "10.244.0.11"}

	t.Log("Test Pods can reach only the mirror and the cluster's DNS Pods.")
	check(
		conn{mirror, "TCP", 8081, true}, // the port of kube.Serve in generate's Deployment
		conn{mirror, "TCP", 8080, false},
		conn{goCache, "TCP", goCachePort, false},
		conn{gofmt, "TCP", mirrorPort, false},
		conn{notMirror, "TCP", mirrorPort, false},
		conn{coreDNS, "UDP", 53, true},
		conn{coreDNS, "TCP", 53, true},
		conn{coreDNS, "TCP", 9153, false},
		conn{apiServer, "UDP", 53, false},
		conn{apiServer, "TCP", 6443, false},
		conn{notMirror, "UDP", 53, false},
		conn{publicDNS, "UDP", 53, false},
		conn{publicDNS, "TCP", 53, false},
		conn{nodeLocalDNS, "UDP", 53, false},
		conn{public, "TCP", 443, false},
		conn{metadata, "TCP", 80, false},
	)

	t.Log("With -goproxy, test Pods can reach ports 80 and 443 outside the cluster, but not the cluster's addresses or a metadata server.")
	set("goproxy", "https://proxy.golang.org")
	check(
		conn{mirror, "TCP", mirrorPort, true},
		conn{coreDNS, "UDP", 53, true},
		conn{public, "TCP", 443, true},
		conn{public, "TCP", 80, true},
		conn{public, "TCP", 6443, false},
		conn{publicDNS, "UDP", 53, false},
		conn{metadata, "TCP", 80, false},
		conn{notMirror, "TCP", 443, false},
		conn{apiServer, "TCP", 443, false},
		conn{node, "TCP", 443, false},
		conn{cgnat, "TCP", 443, false},
		conn{home, "TCP", 80, false},
	)
	set("goproxy", "off")

	t.Log("With -go-cache-namespace, test Pods can also reach go-cache's port on go-cache's Pods.")
	set("go-cache-namespace", "go-cache")
	otherCache := dest{ns: "go-cache", labels: map[string]string{"app": "cache"}, ip: "10.244.0.12"}
	check(
		conn{goCache, "TCP", 8080, true}, // go-cache's -addr, where its Service sends port 80
		conn{goCache, "TCP", 80, false},
		conn{goCache, "UDP", goCachePort, false},
		conn{otherCache, "TCP", goCachePort, false},
		conn{dest{ns: "default", labels: map[string]string{"app.kubernetes.io/name": "go-cache"}, ip: "10.244.1.8"}, "TCP", goCachePort, false},
		conn{mirror, "TCP", mirrorPort, true},
		conn{mirror, "TCP", goCachePort, false},
		conn{coreDNS, "UDP", 53, true},
		conn{public, "TCP", 443, false},
	)
	set("go-cache-labels", "app=cache")
	check(
		conn{otherCache, "TCP", goCachePort, true},
		conn{goCache, "TCP", goCachePort, false},
	)
	set("go-cache-namespace", "")
	check(conn{otherCache, "TCP", goCachePort, false})

	t.Log("The flags choose the mirror's and the DNS servers' Pods, and DNS servers outside Pods.")
	set("mirror-namespace", "vcs")
	set("mirror-labels", "app=mirror,tier=git")
	set("dns-namespace", "openshift-dns")
	set("dns-labels", "dns.operator.openshift.io/daemonset-dns=default")
	set("dns-cidrs", "169.254.20.10/32,fd00::a/128")
	openshiftDNS := dest{ns: "openshift-dns", labels: map[string]string{"dns.operator.openshift.io/daemonset-dns": "default"}, ip: "10.128.0.4"}
	check(
		conn{dest{ns: "vcs", labels: map[string]string{"app": "mirror", "tier": "git", "extra": "x"}, ip: "10.244.0.8"}, "TCP", mirrorPort, true},
		conn{dest{ns: "git-k8s", labels: map[string]string{"app": "mirror", "tier": "git"}, ip: "10.244.0.10"}, "TCP", mirrorPort, false},
		conn{dest{ns: "vcs", labels: map[string]string{"app": "mirror"}, ip: "10.244.0.9"}, "TCP", mirrorPort, false},
		conn{mirror, "TCP", mirrorPort, false},
		conn{openshiftDNS, "UDP", 53, true},
		conn{coreDNS, "UDP", 53, false},
		conn{nodeLocalDNS, "UDP", 53, true},
		conn{nodeLocalDNS, "TCP", 53, true},
		conn{nodeLocalDNS, "TCP", 80, false},
		conn{dest{ip: "169.254.20.11"}, "UDP", 53, false},
		conn{dest{ip: "fd00::a"}, "UDP", 53, true},
	)
}

func TestFlagValues(t *testing.T) {
	var l labels
	if err := l.Set("app=mirror,tier="); err != nil || !maps.Equal(l, labels{"app": "mirror", "tier": ""}) || l.String() != "app=mirror,tier=" {
		t.Errorf("labels = %v (%v), want app=mirror,tier=", l, err)
	}
	for _, s := range []string{"", "app", "=mirror", "app=mirror,"} {
		if err := l.Set(s); err == nil {
			t.Errorf("labels %q are valid", s)
		}
	}
	var c cidrs
	if err := c.Set("169.254.20.10/32,fd00::a/128"); err != nil || c.String() != "169.254.20.10/32,fd00::a/128" {
		t.Errorf("CIDRs = %v (%v), want 169.254.20.10/32,fd00::a/128", c, err)
	}
	if err := c.Set(""); err != nil || c != nil {
		t.Errorf("no CIDRs = %v (%v)", c, err)
	}
	for _, s := range []string{"169.254.20.10", "10.0.0.1/8", "169.254.20.10/32,", "dns"} {
		if err := c.Set(s); err == nil {
			t.Errorf("CIDRs %q are valid", s)
		}
	}
}

// dest is where a test Pod connects to: a Pod with labels in the namespace
// ns, or an address outside Pods if ns is "". A plugin may match a Pod's
// address with an ipBlock, so Pods have addresses too.
type dest struct {
	ns     string
	labels map[string]string
	ip     string
}

// allows reports whether rules let a test Pod connect to port on to. A rule
// without peers allows every address, and one without ports allows every
// port.
func allows(rules []NetworkPolicyRule, to dest, protocol string, port int32) bool {
	return slices.ContainsFunc(rules, func(r NetworkPolicyRule) bool {
		return (len(r.Ports) == 0 || slices.Contains(r.Ports, NetworkPolicyPort{Protocol: protocol, Port: port})) &&
			(len(r.To) == 0 || slices.ContainsFunc(r.To, func(p NetworkPolicyPeer) bool { return selects(p, to) }))
	})
}

// selects reports whether peer selects to. Selectors select only Pods, and
// the only label that a namespace surely has is its name. A peer without a
// namespace selector selects Pods in the test Pod's namespace, default.
func selects(peer NetworkPolicyPeer, to dest) bool {
	if b := peer.IPBlock; b != nil {
		ip := netip.MustParseAddr(to.ip)
		in := func(cidr string) bool { return netip.MustParsePrefix(cidr).Contains(ip) }
		return in(b.CIDR) && !slices.ContainsFunc(b.Except, in)
	}
	if to.ns == "" {
		return false
	}
	nsOK := to.ns == "default"
	if s := peer.NamespaceSelector; s != nil {
		nsOK = subset(s.MatchLabels, map[string]string{"kubernetes.io/metadata.name": to.ns})
	}
	return nsOK && (peer.PodSelector == nil || subset(peer.PodSelector.MatchLabels, to.labels))
}

// subset reports whether have has every label in want.
func subset(want, have map[string]string) bool {
	for k, v := range want {
		if w, ok := have[k]; !ok || w != v {
			return false
		}
	}
	return true
}
