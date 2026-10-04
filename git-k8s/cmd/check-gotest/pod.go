package main

import (
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Pod declares the fields of a Pod that a test Pod sets and the check reads.
// kube's cache stores only these fields, and every write is a server-side
// apply of them.
type Pod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Spec        PodSpec   `json:"spec"`
	Status      PodStatus `json:"status,omitzero"`
}

type PodSpec struct {
	RestartPolicy                string              `json:"restartPolicy,omitempty"`
	AutomountServiceAccountToken *bool               `json:"automountServiceAccountToken,omitempty"`
	ActiveDeadlineSeconds        *int64              `json:"activeDeadlineSeconds,omitempty"`
	RuntimeClassName             string              `json:"runtimeClassName,omitempty"`
	SecurityContext              *PodSecurityContext `json:"securityContext,omitempty"`
	Volumes                      []Volume            `json:"volumes,omitempty"`
	InitContainers               []Container         `json:"initContainers,omitempty"`
	Containers                   []Container         `json:"containers"`
}

type PodSecurityContext struct {
	RunAsNonRoot   *bool           `json:"runAsNonRoot,omitempty"`
	RunAsUser      *int64          `json:"runAsUser,omitempty"`
	RunAsGroup     *int64          `json:"runAsGroup,omitempty"`
	FSGroup        *int64          `json:"fsGroup,omitempty"`
	SeccompProfile *SeccompProfile `json:"seccompProfile,omitempty"`
}

type SeccompProfile struct {
	Type string `json:"type"`
}

type Volume struct {
	Name     string        `json:"name"`
	EmptyDir *EmptyDir     `json:"emptyDir,omitempty"`
	Secret   *SecretVolume `json:"secret,omitempty"`
}

type EmptyDir struct {
	SizeLimit string `json:"sizeLimit,omitempty"`
}

type SecretVolume struct {
	SecretName  string      `json:"secretName"`
	Items       []KeyToPath `json:"items,omitempty"`
	DefaultMode *int32      `json:"defaultMode,omitempty"`
	Optional    *bool       `json:"optional,omitempty"`
}

type KeyToPath struct {
	Key  string `json:"key"`
	Path string `json:"path"`
}

type Container struct {
	Name                     string           `json:"name"`
	Image                    string           `json:"image"`
	ImagePullPolicy          string           `json:"imagePullPolicy,omitempty"`
	Command                  []string         `json:"command,omitempty"`
	WorkingDir               string           `json:"workingDir,omitempty"`
	Env                      []EnvVar         `json:"env,omitempty"`
	VolumeMounts             []VolumeMount    `json:"volumeMounts,omitempty"`
	SecurityContext          *SecurityContext `json:"securityContext,omitempty"`
	TerminationMessagePolicy string           `json:"terminationMessagePolicy,omitempty"`
	Resources                *Resources       `json:"resources,omitempty"`
}

type EnvVar struct {
	Name      string        `json:"name"`
	Value     string        `json:"value,omitempty"`
	ValueFrom *EnvVarSource `json:"valueFrom,omitempty"`
}

type EnvVarSource struct {
	SecretKeyRef *SecretKeySelector `json:"secretKeyRef,omitempty"`
}

type SecretKeySelector struct {
	Name     string `json:"name"`
	Key      string `json:"key"`
	Optional *bool  `json:"optional,omitempty"`
}

type VolumeMount struct {
	Name      string `json:"name"`
	MountPath string `json:"mountPath"`
}

type SecurityContext struct {
	AllowPrivilegeEscalation *bool         `json:"allowPrivilegeEscalation,omitempty"`
	ReadOnlyRootFilesystem   *bool         `json:"readOnlyRootFilesystem,omitempty"`
	Capabilities             *Capabilities `json:"capabilities,omitempty"`
}

type Capabilities struct {
	Drop []string `json:"drop,omitempty"`
}

type Resources struct {
	Requests map[string]k8s.Quantity `json:"requests,omitempty"`
	Limits   map[string]k8s.Quantity `json:"limits,omitempty"`
}

type PodStatus struct {
	Phase                 string            `json:"phase,omitempty"`
	Reason                string            `json:"reason,omitempty"`
	Message               string            `json:"message,omitempty"`
	InitContainerStatuses []ContainerStatus `json:"initContainerStatuses,omitempty"`
	ContainerStatuses     []ContainerStatus `json:"containerStatuses,omitempty"`
}

type ContainerStatus struct {
	Name  string `json:"name"`
	State struct {
		Terminated *Terminated `json:"terminated,omitempty"`
	} `json:"state"`
}

type Terminated struct {
	ExitCode int32  `json:"exitCode"`
	Reason   string `json:"reason,omitempty"`
	Message  string `json:"message,omitempty"`
}
