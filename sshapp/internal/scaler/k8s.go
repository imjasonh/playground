package scaler

import (
	"context"
	"fmt"
	"net"
	"strconv"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/util/wait"
	"k8s.io/client-go/kubernetes"
	"k8s.io/client-go/rest"
	"k8s.io/client-go/tools/clientcmd"
)

// K8sConfig holds how the activator finds and scales its app Deployment.
type K8sConfig struct {
	Namespace    string
	Deployment   string
	Service      string
	Port         int32
	WarmReplicas int32
	IdleAfter    time.Duration
	ScaleToZero  bool
	Kubeconfig   string // empty => in-cluster
}

// NewK8s builds a DeploymentScaler backed by the Kubernetes API.
func NewK8s(cfg K8sConfig) (*DeploymentScaler, error) {
	if cfg.WarmReplicas <= 0 {
		cfg.WarmReplicas = 1
	}
	if cfg.Port <= 0 {
		cfg.Port = 2222
	}

	restCfg, err := restConfig(cfg.Kubeconfig)
	if err != nil {
		return nil, err
	}
	client, err := kubernetes.NewForConfig(restCfg)
	if err != nil {
		return nil, err
	}

	s := &DeploymentScaler{
		WarmReplicas: cfg.WarmReplicas,
		IdleAfter:    cfg.IdleAfter,
		ScaleToZero:  cfg.ScaleToZero,
		ScaleUp: func(ctx context.Context, replicas int32) error {
			return setReplicas(ctx, client, cfg.Namespace, cfg.Deployment, replicas)
		},
		ScaleDown: func(ctx context.Context) error {
			return setReplicas(ctx, client, cfg.Namespace, cfg.Deployment, 0)
		},
		ReadyAddr: func(ctx context.Context) (string, error) {
			return waitReadyAddr(ctx, client, cfg.Namespace, cfg.Service, cfg.Port)
		},
	}

	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	if err := SyncFromDeployment(ctx, s, client, cfg.Namespace, cfg.Deployment); err != nil {
		// Deployment may not exist yet on first apply; treat as cold.
		MarkScaled(s, false)
	} else if sHasReplicas(s) {
		// Already warm (for example activator restart). Arm idle scale-down.
		s.SetActiveConnections(0)
	}
	return s, nil
}

func sHasReplicas(s *DeploymentScaler) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.scaled
}

func restConfig(kubeconfig string) (*rest.Config, error) {
	if kubeconfig != "" {
		return clientcmd.BuildConfigFromFlags("", kubeconfig)
	}
	return rest.InClusterConfig()
}

func setReplicas(ctx context.Context, client kubernetes.Interface, ns, name string, replicas int32) error {
	scale, err := client.AppsV1().Deployments(ns).GetScale(ctx, name, metav1.GetOptions{})
	if err != nil {
		return err
	}
	if scale.Spec.Replicas == replicas {
		return nil
	}
	scale.Spec.Replicas = replicas
	_, err = client.AppsV1().Deployments(ns).UpdateScale(ctx, name, scale, metav1.UpdateOptions{})
	return err
}

func waitReadyAddr(ctx context.Context, client kubernetes.Interface, ns, service string, port int32) (string, error) {
	var addr string
	if err := wait.PollUntilContextCancel(ctx, 500*time.Millisecond, true, func(ctx context.Context) (bool, error) {
		eps, err := client.CoreV1().Endpoints(ns).Get(ctx, service, metav1.GetOptions{})
		if err != nil {
			return false, nil
		}
		ip := firstReadyIP(eps)
		if ip == "" {
			return false, nil
		}
		addr = net.JoinHostPort(ip, strconv.Itoa(int(port)))
		return true, nil
	}); err != nil {
		return "", fmt.Errorf("wait for endpoints %s/%s: %w", ns, service, err)
	}
	return addr, nil
}

func firstReadyIP(eps *corev1.Endpoints) string {
	for _, sub := range eps.Subsets {
		for _, addr := range sub.Addresses {
			if addr.IP != "" {
				return addr.IP
			}
		}
	}
	return ""
}

// MarkScaled lets tests/tools seed the scaler after reading current replicas.
func MarkScaled(s *DeploymentScaler, scaled bool) {
	s.mu.Lock()
	s.scaled = scaled
	s.mu.Unlock()
}

// SyncFromDeployment sets scaled from the live Deployment replica count.
func SyncFromDeployment(ctx context.Context, s *DeploymentScaler, client kubernetes.Interface, ns, name string) error {
	dep, err := client.AppsV1().Deployments(ns).Get(ctx, name, metav1.GetOptions{})
	if err != nil {
		return err
	}
	MarkScaled(s, deploymentReplicas(dep) > 0)
	return nil
}

func deploymentReplicas(dep *appsv1.Deployment) int32 {
	if dep.Spec.Replicas == nil {
		return 1
	}
	return *dep.Spec.Replicas
}
