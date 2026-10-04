package main

import (
	"flag"
	"fmt"
	"maps"
	"net/netip"
	"slices"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// The test Pods of check-gotest run a branch's code. This program owns their
// NetworkPolicy, so that check-gotest, which creates Pods in the
// repositories' namespaces, can't change NetworkPolicies.
var (
	goProxy  = flag.String("goproxy", "off", "check-gotest's -goproxy; unless it's off, test Pods can reach ports 80 and 443 on public IPv4 addresses")
	mirrorNS = flag.String("mirror-namespace", "git-k8s", "namespace of this program's Pods, where test Pods reach the mirror")
	dnsNS    = flag.String("dns-namespace", "kube-system", "namespace of the cluster's DNS Pods")
)

var (
	mirrorLabels = labels{"app.kubernetes.io/name": "git-k8s"}
	dnsLabels    = labels{"k8s-app": "kube-dns"}
	dnsCIDRs     cidrs
)

func init() {
	flag.Var(&mirrorLabels, "mirror-labels", "labels of this program's Pods, as KEY=VALUE[,KEY=VALUE]")
	flag.Var(&dnsLabels, "dns-labels", "labels of the cluster's DNS Pods, as KEY=VALUE[,KEY=VALUE]")
	flag.Var(&dnsCIDRs, "dns-cidrs", "CIDRs of DNS servers that test Pods can also reach, such as NodeLocal DNSCache's 169.254.20.10/32, separated by commas")
}

// labels is a flag that holds the labels that a selector matches.
type labels map[string]string

func (l labels) String() string {
	var s []string
	for _, k := range slices.Sorted(maps.Keys(l)) {
		s = append(s, k+"="+l[k])
	}
	return strings.Join(s, ",")
}

// Set requires at least one label, because a selector with none matches
// every Pod in the namespace.
func (l *labels) Set(s string) error {
	m := labels{}
	for kv := range strings.SplitSeq(s, ",") {
		k, v, ok := strings.Cut(kv, "=")
		if !ok || k == "" {
			return fmt.Errorf("%q isn't KEY=VALUE", kv)
		}
		m[k] = v
	}
	*l = m
	return nil
}

// cidrs is a flag that holds CIDRs.
type cidrs []netip.Prefix

func (c cidrs) String() string {
	s := make([]string, len(c))
	for i, p := range c {
		s[i] = p.String()
	}
	return strings.Join(s, ",")
}

func (c *cidrs) Set(s string) error {
	var ps cidrs
	if s == "" {
		*c = ps
		return nil
	}
	for v := range strings.SplitSeq(s, ",") {
		p, err := netip.ParsePrefix(v)
		if err != nil {
			return err
		}
		if p != p.Masked() {
			return fmt.Errorf("%s has bits set after its prefix length; did you mean %s?", p, p.Masked())
		}
		ps = append(ps, p)
	}
	*c = ps
	return nil
}

// mirrorPort is the port of this program's Pods that serves the mirror. A
// NetworkPolicy matches the port of the Pod that a Service sends a
// connection to, not the Service's port.
const mirrorPort = 8081

// privateRanges are the IPv4 ranges where a cluster's Pods, Services, and
// nodes, and a cloud's metadata server, usually are: the private ranges,
// the shared address space, and the link-local range.
var privateRanges = []string{"10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16", "100.64.0.0/10", "169.254.0.0/16"}

// testPodsPolicy declares the NetworkPolicy, REPOSITORY-test-pods, that
// repo owns for the test Pods in its namespace. It selects the Pods with
// kube's controller label for check-gotest, which are the Pods that the
// mirror lets fetch, so the policies of the repositories in a namespace are
// the same, and each one covers every test Pod there. It lets the Pods
// reach the mirror's port on this program's Pods, and port 53 on the DNS
// Pods and -dns-cidrs, and lets nothing reach them. With -goproxy, it also
// lets them reach ports 80 and 443 on IPv4 addresses outside privateRanges,
// which is where a public module proxy is. On a cluster that gives Pods,
// Services, or nodes addresses outside privateRanges, that rule lets test
// Pods reach them too.
func testPodsPolicy(repo *gitk8s.GitRepository) *NetworkPolicy {
	dns := []NetworkPolicyPeer{{NamespaceSelector: namespace(*dnsNS), PodSelector: &LabelSelector{MatchLabels: maps.Clone(dnsLabels)}}}
	for _, c := range dnsCIDRs {
		dns = append(dns, NetworkPolicyPeer{IPBlock: &IPBlock{CIDR: c.String()}})
	}
	p := &NetworkPolicy{Object: kube.Meta(repo.Name+"-test-pods", nil)}
	p.Spec = NetworkPolicySpec{
		PodSelector: LabelSelector{MatchLabels: map[string]string{gitk8s.ControllerLabel: gitk8s.GoTestController}},
		PolicyTypes: []string{"Ingress", "Egress"},
		Egress: []NetworkPolicyRule{{
			To:    []NetworkPolicyPeer{{NamespaceSelector: namespace(*mirrorNS), PodSelector: &LabelSelector{MatchLabels: maps.Clone(mirrorLabels)}}},
			Ports: []NetworkPolicyPort{{Protocol: "TCP", Port: mirrorPort}},
		}, {
			To:    dns,
			Ports: []NetworkPolicyPort{{Protocol: "UDP", Port: 53}, {Protocol: "TCP", Port: 53}},
		}},
	}
	if *goProxy != "off" {
		p.Spec.Egress = append(p.Spec.Egress, NetworkPolicyRule{
			To:    []NetworkPolicyPeer{{IPBlock: &IPBlock{CIDR: "0.0.0.0/0", Except: slices.Clone(privateRanges)}}},
			Ports: []NetworkPolicyPort{{Protocol: "TCP", Port: 80}, {Protocol: "TCP", Port: 443}},
		})
	}
	return p
}

// namespace selects the namespace named name.
func namespace(name string) *LabelSelector {
	return &LabelSelector{MatchLabels: map[string]string{"kubernetes.io/metadata.name": name}}
}

// NetworkPolicy declares the fields of a NetworkPolicy that the test Pods'
// policy sets.
type NetworkPolicy struct {
	kube.Object `kube:"apiVersion=networking.k8s.io/v1,kind=NetworkPolicy,plural=networkpolicies,scope=Namespaced"`
	Spec        NetworkPolicySpec `json:"spec"`
}

type NetworkPolicySpec struct {
	PodSelector LabelSelector       `json:"podSelector"`
	PolicyTypes []string            `json:"policyTypes"`
	Egress      []NetworkPolicyRule `json:"egress,omitempty"`
}

type LabelSelector struct {
	MatchLabels map[string]string `json:"matchLabels,omitempty"`
}

type NetworkPolicyRule struct {
	To    []NetworkPolicyPeer `json:"to,omitempty"`
	Ports []NetworkPolicyPort `json:"ports,omitempty"`
}

type NetworkPolicyPeer struct {
	NamespaceSelector *LabelSelector `json:"namespaceSelector,omitempty"`
	PodSelector       *LabelSelector `json:"podSelector,omitempty"`
	IPBlock           *IPBlock       `json:"ipBlock,omitempty"`
}

type IPBlock struct {
	CIDR   string   `json:"cidr"`
	Except []string `json:"except,omitempty"`
}

type NetworkPolicyPort struct {
	Protocol string `json:"protocol"`
	Port     int32  `json:"port"`
}
