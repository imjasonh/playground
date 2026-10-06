package agent

import (
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Pod declares the fields of a Pod that an agent Pod sets and the runner
// reads. kube's cache stores only these fields, and every write is a
// server-side apply of them.
type Pod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Spec        PodSpec   `json:"spec"`
	Status      PodStatus `json:"status,omitzero"`
}

type PodSpec struct {
	RestartPolicy                 string              `json:"restartPolicy,omitempty"`
	AutomountServiceAccountToken  *bool               `json:"automountServiceAccountToken,omitempty"`
	EnableServiceLinks            *bool               `json:"enableServiceLinks,omitempty"`
	ActiveDeadlineSeconds         *int64              `json:"activeDeadlineSeconds,omitempty"`
	TerminationGracePeriodSeconds *int64              `json:"terminationGracePeriodSeconds,omitempty"`
	RuntimeClassName              string              `json:"runtimeClassName,omitempty"`
	SecurityContext               *PodSecurityContext `json:"securityContext,omitempty"`
	Volumes                       []Volume            `json:"volumes,omitempty"`
	InitContainers                []Container         `json:"initContainers,omitempty"`
	Containers                    []Container         `json:"containers"`
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
	Name      string     `json:"name"`
	EmptyDir  *EmptyDir  `json:"emptyDir,omitempty"`
	Projected *Projected `json:"projected,omitempty"`
}

type EmptyDir struct {
	Medium    string `json:"medium,omitempty"`
	SizeLimit string `json:"sizeLimit,omitempty"`
}

type Projected struct {
	Sources []VolumeProjection `json:"sources"`
}

type VolumeProjection struct {
	ServiceAccountToken *ServiceAccountToken `json:"serviceAccountToken,omitempty"`
}

type ServiceAccountToken struct {
	Audience          string `json:"audience"`
	ExpirationSeconds *int64 `json:"expirationSeconds,omitempty"`
	Path              string `json:"path"`
}

type Container struct {
	Name                     string           `json:"name"`
	Image                    string           `json:"image"`
	ImagePullPolicy          string           `json:"imagePullPolicy,omitempty"`
	Command                  []string         `json:"command,omitempty"`
	Args                     []string         `json:"args,omitempty"`
	Env                      []EnvVar         `json:"env,omitempty"`
	Ports                    []ContainerPort  `json:"ports,omitempty"`
	VolumeMounts             []VolumeMount    `json:"volumeMounts,omitempty"`
	SecurityContext          *SecurityContext `json:"securityContext,omitempty"`
	TerminationMessagePolicy string           `json:"terminationMessagePolicy,omitempty"`
	Resources                *Resources       `json:"resources,omitempty"`
}

type ContainerPort struct {
	Name          string `json:"name,omitempty"`
	ContainerPort int32  `json:"containerPort"`
	Protocol      string `json:"protocol,omitempty"`
}

type EnvVar struct {
	Name      string        `json:"name"`
	Value     string        `json:"value,omitempty"`
	ValueFrom *EnvVarSource `json:"valueFrom,omitempty"`
}

type EnvVarSource struct {
	SecretKeyRef *SecretKeySelector `json:"secretKeyRef,omitempty"`
	FieldRef     *FieldSelector     `json:"fieldRef,omitempty"`
}

type SecretKeySelector struct {
	Name     string `json:"name"`
	Key      string `json:"key"`
	Optional *bool  `json:"optional,omitempty"`
}

type FieldSelector struct {
	FieldPath string `json:"fieldPath"`
}

type VolumeMount struct {
	Name      string `json:"name"`
	MountPath string `json:"mountPath"`
	ReadOnly  bool   `json:"readOnly,omitempty"`
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
	PodIP                 string            `json:"podIP,omitempty"`
	StartTime             time.Time         `json:"startTime,omitzero"`
	Conditions            []PodCondition    `json:"conditions,omitempty"`
	InitContainerStatuses []ContainerStatus `json:"initContainerStatuses,omitempty"`
	ContainerStatuses     []ContainerStatus `json:"containerStatuses,omitempty"`
}

type PodCondition struct {
	Type    string `json:"type"`
	Status  string `json:"status"`
	Reason  string `json:"reason,omitempty"`
	Message string `json:"message,omitempty"`
}

type ContainerStatus struct {
	Name  string         `json:"name"`
	State ContainerState `json:"state"`
}

type ContainerState struct {
	Waiting    *Waiting    `json:"waiting,omitempty"`
	Running    *Running    `json:"running,omitempty"`
	Terminated *Terminated `json:"terminated,omitempty"`
}

type Waiting struct {
	Reason  string `json:"reason,omitempty"`
	Message string `json:"message,omitempty"`
}

type Running struct {
	StartedAt time.Time `json:"startedAt,omitzero"`
}

type Terminated struct {
	ExitCode   int32     `json:"exitCode"`
	Reason     string    `json:"reason,omitempty"`
	Message    string    `json:"message,omitempty"`
	FinishedAt time.Time `json:"finishedAt,omitzero"`
}

// podPhase is what the runner counts unfinished agent Pods by. Declaring
// only the phase means that other changes to Pods don't run the check again.
type podPhase struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Status      struct {
		Phase string `json:"phase,omitempty"`
	} `json:"status"`
}
