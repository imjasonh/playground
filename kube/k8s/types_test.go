package k8s_test

import (
	"encoding/json"
	"reflect"
	"testing"

	"github.com/imjasonh/playground/kube/k8s"
)

// TestNestedTypes builds desired objects from the named types of nested
// fields, and checks the JSON that they encode to and decode from.
func TestNestedTypes(t *testing.T) {
	yes, two, class := true, int32(2), "nginx"
	for _, tc := range []struct {
		name string
		v    any
		want string
	}{
		{"label selector", k8s.LabelSelector{MatchExpressions: []k8s.LabelSelectorRequirement{{Key: "tier", Operator: "In", Values: []string{"web"}}}},
			`{"matchExpressions":[{"key":"tier","operator":"In","values":["web"]}]}`},
		{"pod spec", k8s.PodSpec{
			Containers: []k8s.Container{{
				Name:           "app",
				Env:            []k8s.EnvVar{{Name: "POD", ValueFrom: &k8s.EnvVarSource{FieldRef: &k8s.ObjectFieldSelector{FieldPath: "metadata.name"}}}},
				ReadinessProbe: &k8s.Probe{HTTPGet: &k8s.HTTPGetAction{Path: "/healthz", Port: k8s.Int(8080)}},
				LivenessProbe:  &k8s.Probe{TCPSocket: &k8s.TCPSocketAction{Port: k8s.Str("http")}},
			}},
			Volumes: []k8s.Volume{
				{Name: "a", ConfigMap: &k8s.ConfigMapVolumeSource{Name: "settings", Optional: &yes}},
				{Name: "b", Secret: &k8s.SecretVolumeSource{SecretName: "token"}},
				{Name: "c", EmptyDir: &k8s.EmptyDirVolumeSource{SizeLimit: "1Gi"}},
				{Name: "d", PersistentVolumeClaim: &k8s.PersistentVolumeClaimVolumeSource{ClaimName: "data", ReadOnly: true}},
			},
			ImagePullSecrets: []k8s.LocalObjectReference{{Name: "registry"}},
		}, `{"containers":[{"name":"app","env":[{"name":"POD","valueFrom":{"fieldRef":{"fieldPath":"metadata.name"}}}],` +
			`"readinessProbe":{"httpGet":{"path":"/healthz","port":8080}},"livenessProbe":{"tcpSocket":{"port":"http"}}}],` +
			`"volumes":[{"name":"a","configMap":{"name":"settings","optional":true}},{"name":"b","secret":{"secretName":"token"}},` +
			`{"name":"c","emptyDir":{"sizeLimit":"1Gi"}},{"name":"d","persistentVolumeClaim":{"claimName":"data","readOnly":true}}],` +
			`"imagePullSecrets":[{"name":"registry"}]}`},
		{"exec probe", k8s.Probe{Exec: &k8s.ExecAction{Command: []string{"true"}}}, `{"exec":{"command":["true"]}}`},
		{"node spec", k8s.NodeSpec{Taints: []k8s.Taint{{Key: "dedicated", Value: "gpu", Effect: "NoSchedule"}}},
			`{"taints":[{"key":"dedicated","value":"gpu","effect":"NoSchedule"}]}`},
		{"resource quota spec", k8s.ResourceQuotaSpec{Hard: map[string]k8s.Quantity{"pods": "10"}}, `{"hard":{"pods":"10"}}`},
		{"job spec", k8s.JobSpec{BackoffLimit: &two, Template: k8s.PodTemplateSpec{Spec: k8s.PodSpec{RestartPolicy: "Never"}}},
			`{"backoffLimit":2,"template":{"spec":{"restartPolicy":"Never"}}}`},
		{"ingress spec", k8s.IngressSpec{
			IngressClassName: &class,
			TLS:              []k8s.IngressTLS{{Hosts: []string{"example.com"}, SecretName: "tls"}},
			Rules: []k8s.IngressRule{{Host: "example.com", HTTP: &k8s.HTTPIngressRuleValue{Paths: []k8s.IngressPath{{
				Path:     "/",
				PathType: "Prefix",
				Backend:  k8s.IngressBackend{Service: k8s.IngressServiceBackend{Name: "web", Port: k8s.ServiceBackendPort{Number: 80}}},
			}}}}},
		}, `{"ingressClassName":"nginx","tls":[{"hosts":["example.com"],"secretName":"tls"}],` +
			`"rules":[{"host":"example.com","http":{"paths":[{"path":"/","pathType":"Prefix","backend":{"service":{"name":"web","port":{"number":80}}}}]}}]}`},
	} {
		b, err := json.Marshal(tc.v)
		if err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		if string(b) != tc.want {
			t.Errorf("%s encodes to\n%s\nwant\n%s", tc.name, b, tc.want)
		}
		got := reflect.New(reflect.TypeOf(tc.v))
		if err := json.Unmarshal([]byte(tc.want), got.Interface()); err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		if !reflect.DeepEqual(got.Elem().Interface(), tc.v) {
			t.Errorf("%s decodes to %+v, want %+v", tc.name, got.Elem().Interface(), tc.v)
		}
	}
}
