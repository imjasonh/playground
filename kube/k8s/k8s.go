// Package k8s has Go types for common built-in Kubernetes objects, for use
// with package kube.
//
// Each type declares the fields that controllers commonly read or set, not
// every field the API has. The cache stores only declared fields, so a
// smaller type uses less memory. When you need a field that isn't here, or
// want a smaller cache, define your own type with the same apiVersion and
// kind; any struct that embeds kube.Object works.
//
// Optional fields are pointers or have omitempty, so that a desired object
// you pass to kube.Own or kube.Apply sets only the fields you assign.
package k8s

import (
	"encoding/json"
	"strconv"

	"github.com/imjasonh/playground/kube"
)

// IntOrString holds an integer or a string, as some fields such as
// Service.Spec.Ports[].TargetPort do. Its zero value is the integer 0.
type IntOrString struct {
	IntVal int32
	StrVal string
	IsStr  bool
}

// Int returns an IntOrString that holds i.
func Int(i int32) IntOrString { return IntOrString{IntVal: i} }

// Str returns an IntOrString that holds s.
func Str(s string) IntOrString { return IntOrString{StrVal: s, IsStr: true} }

func (v IntOrString) String() string {
	if v.IsStr {
		return v.StrVal
	}
	return strconv.Itoa(int(v.IntVal))
}

// MarshalJSON writes a JSON number or string.
func (v IntOrString) MarshalJSON() ([]byte, error) {
	if v.IsStr {
		return json.Marshal(v.StrVal)
	}
	return json.Marshal(v.IntVal)
}

// UnmarshalJSON reads a JSON number or string.
func (v *IntOrString) UnmarshalJSON(b []byte) error {
	if len(b) > 0 && b[0] == '"' {
		v.IsStr, v.IntVal = true, 0
		return json.Unmarshal(b, &v.StrVal)
	}
	v.IsStr, v.StrVal = false, ""
	return json.Unmarshal(b, &v.IntVal)
}

// OpenAPISchema describes IntOrString in a CustomResourceDefinition.
func (IntOrString) OpenAPISchema() map[string]any {
	return map[string]any{"x-kubernetes-int-or-string": true}
}

// Quantity is a resource amount such as "500m" or "1Gi".
type Quantity string

// OpenAPISchema describes Quantity in a CustomResourceDefinition.
func (Quantity) OpenAPISchema() map[string]any {
	return map[string]any{"x-kubernetes-int-or-string": true, "anyOf": []any{map[string]any{"type": "integer"}, map[string]any{"type": "string"}}}
}

// LabelSelector selects objects by label.
type LabelSelector struct {
	MatchLabels      map[string]string `json:"matchLabels,omitempty"`
	MatchExpressions []struct {
		Key      string   `json:"key"`
		Operator string   `json:"operator"`
		Values   []string `json:"values,omitempty"`
	} `json:"matchExpressions,omitempty"`
}

// TemplateMeta is the metadata of a pod template.
type TemplateMeta struct {
	Labels      map[string]string `json:"labels,omitempty"`
	Annotations map[string]string `json:"annotations,omitempty"`
}

// PodTemplateSpec describes the pods that a workload creates.
type PodTemplateSpec struct {
	Metadata TemplateMeta `json:"metadata,omitzero"`
	Spec     PodSpec      `json:"spec,omitzero"`
}

// PodSpec describes a pod.
type PodSpec struct {
	Containers                    []Container       `json:"containers,omitempty"`
	InitContainers                []Container       `json:"initContainers,omitempty"`
	Volumes                       []Volume          `json:"volumes,omitempty"`
	ServiceAccountName            string            `json:"serviceAccountName,omitempty"`
	NodeName                      string            `json:"nodeName,omitempty"`
	NodeSelector                  map[string]string `json:"nodeSelector,omitempty"`
	RestartPolicy                 string            `json:"restartPolicy,omitempty"`
	TerminationGracePeriodSeconds *int64            `json:"terminationGracePeriodSeconds,omitempty"`
	ImagePullSecrets              []struct {
		Name string `json:"name"`
	} `json:"imagePullSecrets,omitempty"`
}

// Container is one container in a pod.
type Container struct {
	Name            string               `json:"name"`
	Image           string               `json:"image,omitempty"`
	ImagePullPolicy string               `json:"imagePullPolicy,omitempty"`
	Command         []string             `json:"command,omitempty"`
	Args            []string             `json:"args,omitempty"`
	WorkingDir      string               `json:"workingDir,omitempty"`
	Env             []EnvVar             `json:"env,omitempty"`
	EnvFrom         []EnvFromSource      `json:"envFrom,omitempty"`
	Ports           []ContainerPort      `json:"ports,omitempty"`
	Resources       ResourceRequirements `json:"resources,omitzero"`
	VolumeMounts    []VolumeMount        `json:"volumeMounts,omitempty"`
	ReadinessProbe  *Probe               `json:"readinessProbe,omitempty"`
	LivenessProbe   *Probe               `json:"livenessProbe,omitempty"`
}

// EnvVar sets one environment variable.
type EnvVar struct {
	Name      string        `json:"name"`
	Value     string        `json:"value,omitempty"`
	ValueFrom *EnvVarSource `json:"valueFrom,omitempty"`
}

// EnvVarSource reads an environment variable's value from elsewhere.
type EnvVarSource struct {
	ConfigMapKeyRef *KeySelector `json:"configMapKeyRef,omitempty"`
	SecretKeyRef    *KeySelector `json:"secretKeyRef,omitempty"`
	FieldRef        *struct {
		FieldPath string `json:"fieldPath"`
	} `json:"fieldRef,omitempty"`
}

// KeySelector names one key of a ConfigMap or Secret.
type KeySelector struct {
	Name     string `json:"name"`
	Key      string `json:"key"`
	Optional *bool  `json:"optional,omitempty"`
}

// EnvFromSource sets environment variables from every key of a ConfigMap or
// Secret.
type EnvFromSource struct {
	Prefix       string     `json:"prefix,omitempty"`
	ConfigMapRef *LocalName `json:"configMapRef,omitempty"`
	SecretRef    *LocalName `json:"secretRef,omitempty"`
}

// LocalName names an object in the same namespace.
type LocalName struct {
	Name     string `json:"name"`
	Optional *bool  `json:"optional,omitempty"`
}

// ContainerPort is a port a container listens on.
type ContainerPort struct {
	Name          string `json:"name,omitempty"`
	ContainerPort int32  `json:"containerPort"`
	Protocol      string `json:"protocol,omitempty"`
}

// ResourceRequirements are a container's resource requests and limits.
type ResourceRequirements struct {
	Requests map[string]Quantity `json:"requests,omitempty"`
	Limits   map[string]Quantity `json:"limits,omitempty"`
}

// VolumeMount mounts a volume into a container.
type VolumeMount struct {
	Name      string `json:"name"`
	MountPath string `json:"mountPath"`
	SubPath   string `json:"subPath,omitempty"`
	ReadOnly  bool   `json:"readOnly,omitempty"`
}

// Volume is a pod volume.
type Volume struct {
	Name      string `json:"name"`
	ConfigMap *struct {
		Name     string `json:"name"`
		Optional *bool  `json:"optional,omitempty"`
	} `json:"configMap,omitempty"`
	Secret *struct {
		SecretName string `json:"secretName"`
		Optional   *bool  `json:"optional,omitempty"`
	} `json:"secret,omitempty"`
	EmptyDir *struct {
		Medium    string   `json:"medium,omitempty"`
		SizeLimit Quantity `json:"sizeLimit,omitempty"`
	} `json:"emptyDir,omitempty"`
	PersistentVolumeClaim *struct {
		ClaimName string `json:"claimName"`
		ReadOnly  bool   `json:"readOnly,omitempty"`
	} `json:"persistentVolumeClaim,omitempty"`
}

// Probe checks a container's health.
type Probe struct {
	HTTPGet *struct {
		Path string      `json:"path,omitempty"`
		Port IntOrString `json:"port"`
	} `json:"httpGet,omitempty"`
	TCPSocket *struct {
		Port IntOrString `json:"port"`
	} `json:"tcpSocket,omitempty"`
	Exec *struct {
		Command []string `json:"command,omitempty"`
	} `json:"exec,omitempty"`
	InitialDelaySeconds int32 `json:"initialDelaySeconds,omitempty"`
	PeriodSeconds       int32 `json:"periodSeconds,omitempty"`
	FailureThreshold    int32 `json:"failureThreshold,omitempty"`
}

// Condition is the condition type that built-in objects use.
type Condition struct {
	Type    string `json:"type"`
	Status  string `json:"status"`
	Reason  string `json:"reason,omitempty"`
	Message string `json:"message,omitempty"`
}

// ConfigMap holds configuration data.
type ConfigMap struct {
	kube.Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Data        map[string]string `json:"data,omitempty"`
	BinaryData  map[string][]byte `json:"binaryData,omitempty"`
	Immutable   *bool             `json:"immutable,omitempty"`
}

// Secret holds sensitive data. Data values are the decoded bytes.
type Secret struct {
	kube.Object `kube:"apiVersion=v1,kind=Secret,plural=secrets,scope=Namespaced"`
	Type        string            `json:"type,omitempty"`
	Data        map[string][]byte `json:"data,omitempty"`
	Immutable   *bool             `json:"immutable,omitempty"`
}

// Namespace is a cluster-scoped namespace.
type Namespace struct {
	kube.Object `kube:"apiVersion=v1,kind=Namespace,plural=namespaces,scope=Cluster"`
	Status      struct {
		Phase string `json:"phase,omitempty"`
	} `json:"status,omitzero"`
}

// ServiceAccount is an identity for pods.
type ServiceAccount struct {
	kube.Object `kube:"apiVersion=v1,kind=ServiceAccount,plural=serviceaccounts,scope=Namespaced"`
}

// Service exposes pods on the network.
type Service struct {
	kube.Object `kube:"apiVersion=v1,kind=Service,plural=services,scope=Namespaced"`
	Spec        ServiceSpec `json:"spec,omitzero"`
	Status      struct {
		LoadBalancer struct {
			Ingress []struct {
				IP       string `json:"ip,omitempty"`
				Hostname string `json:"hostname,omitempty"`
			} `json:"ingress,omitempty"`
		} `json:"loadBalancer,omitzero"`
	} `json:"status,omitzero"`
}

// ServiceSpec describes a Service.
type ServiceSpec struct {
	Type      string            `json:"type,omitempty"`
	Selector  map[string]string `json:"selector,omitempty"`
	Ports     []ServicePort     `json:"ports,omitempty"`
	ClusterIP string            `json:"clusterIP,omitempty"`
}

// ServicePort is one port of a Service.
type ServicePort struct {
	Name       string      `json:"name,omitempty"`
	Protocol   string      `json:"protocol,omitempty"`
	Port       int32       `json:"port"`
	TargetPort IntOrString `json:"targetPort,omitzero"`
	NodePort   int32       `json:"nodePort,omitempty"`
}

// Pod is a group of containers on one node.
type Pod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Spec        PodSpec `json:"spec,omitzero"`
	Status      struct {
		Phase      string      `json:"phase,omitempty"`
		PodIP      string      `json:"podIP,omitempty"`
		Conditions []Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// Node is a machine in the cluster.
type Node struct {
	kube.Object `kube:"apiVersion=v1,kind=Node,plural=nodes,scope=Cluster"`
	Spec        struct {
		Unschedulable bool `json:"unschedulable,omitempty"`
		Taints        []struct {
			Key    string `json:"key"`
			Value  string `json:"value,omitempty"`
			Effect string `json:"effect"`
		} `json:"taints,omitempty"`
	} `json:"spec,omitzero"`
	Status struct {
		Capacity    map[string]Quantity `json:"capacity,omitempty"`
		Allocatable map[string]Quantity `json:"allocatable,omitempty"`
		Conditions  []Condition         `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// ResourceQuota limits the resources a namespace can use.
type ResourceQuota struct {
	kube.Object `kube:"apiVersion=v1,kind=ResourceQuota,plural=resourcequotas,scope=Namespaced"`
	Spec        struct {
		Hard map[string]Quantity `json:"hard,omitempty"`
	} `json:"spec,omitzero"`
}

// Deployment manages a replicated set of pods.
type Deployment struct {
	kube.Object `kube:"apiVersion=apps/v1,kind=Deployment,plural=deployments,scope=Namespaced"`
	Spec        DeploymentSpec   `json:"spec,omitzero"`
	Status      DeploymentStatus `json:"status,omitzero"`
}

// DeploymentSpec describes a Deployment.
type DeploymentSpec struct {
	Replicas *int32          `json:"replicas,omitempty"`
	Selector *LabelSelector  `json:"selector,omitempty"`
	Template PodTemplateSpec `json:"template,omitzero"`
	Paused   bool            `json:"paused,omitempty"`
}

// DeploymentStatus is a Deployment's observed state.
type DeploymentStatus struct {
	ObservedGeneration int64       `json:"observedGeneration,omitempty"`
	Replicas           int32       `json:"replicas,omitempty"`
	UpdatedReplicas    int32       `json:"updatedReplicas,omitempty"`
	ReadyReplicas      int32       `json:"readyReplicas,omitempty"`
	AvailableReplicas  int32       `json:"availableReplicas,omitempty"`
	Conditions         []Condition `json:"conditions,omitempty"`
}

// Job runs pods until a number of them succeed.
type Job struct {
	kube.Object `kube:"apiVersion=batch/v1,kind=Job,plural=jobs,scope=Namespaced"`
	Spec        struct {
		BackoffLimit            *int32          `json:"backoffLimit,omitempty"`
		TTLSecondsAfterFinished *int32          `json:"ttlSecondsAfterFinished,omitempty"`
		Template                PodTemplateSpec `json:"template,omitzero"`
	} `json:"spec,omitzero"`
	Status struct {
		Active     int32       `json:"active,omitempty"`
		Succeeded  int32       `json:"succeeded,omitempty"`
		Failed     int32       `json:"failed,omitempty"`
		Conditions []Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// PolicyRule grants verbs on resources.
type PolicyRule struct {
	APIGroups     []string `json:"apiGroups,omitempty"`
	Resources     []string `json:"resources,omitempty"`
	ResourceNames []string `json:"resourceNames,omitempty"`
	Verbs         []string `json:"verbs"`
}

// Subject is a user, group, or service account that a binding grants to.
type Subject struct {
	Kind      string `json:"kind"`
	Name      string `json:"name"`
	Namespace string `json:"namespace,omitempty"`
	APIGroup  string `json:"apiGroup,omitempty"`
}

// RoleRef names the role that a binding grants.
type RoleRef struct {
	APIGroup string `json:"apiGroup"`
	Kind     string `json:"kind"`
	Name     string `json:"name"`
}

// Role grants permissions in one namespace.
type Role struct {
	kube.Object `kube:"apiVersion=rbac.authorization.k8s.io/v1,kind=Role,plural=roles,scope=Namespaced"`
	Rules       []PolicyRule `json:"rules,omitempty"`
}

// RoleBinding grants a Role or ClusterRole in one namespace.
type RoleBinding struct {
	kube.Object `kube:"apiVersion=rbac.authorization.k8s.io/v1,kind=RoleBinding,plural=rolebindings,scope=Namespaced"`
	Subjects    []Subject `json:"subjects,omitempty"`
	RoleRef     RoleRef   `json:"roleRef"`
}

// Ingress routes HTTP traffic to Services.
type Ingress struct {
	kube.Object `kube:"apiVersion=networking.k8s.io/v1,kind=Ingress,plural=ingresses,scope=Namespaced"`
	Spec        struct {
		IngressClassName *string `json:"ingressClassName,omitempty"`
		TLS              []struct {
			Hosts      []string `json:"hosts,omitempty"`
			SecretName string   `json:"secretName,omitempty"`
		} `json:"tls,omitempty"`
		Rules []IngressRule `json:"rules,omitempty"`
	} `json:"spec,omitzero"`
}

// IngressRule routes one host's paths.
type IngressRule struct {
	Host string `json:"host,omitempty"`
	HTTP *struct {
		Paths []IngressPath `json:"paths"`
	} `json:"http,omitempty"`
}

// IngressPath routes one path to a Service port.
type IngressPath struct {
	Path     string `json:"path,omitempty"`
	PathType string `json:"pathType"`
	Backend  struct {
		Service struct {
			Name string `json:"name"`
			Port struct {
				Number int32  `json:"number,omitempty"`
				Name   string `json:"name,omitempty"`
			} `json:"port"`
		} `json:"service"`
	} `json:"backend"`
}
