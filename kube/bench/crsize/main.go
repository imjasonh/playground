// Command crsize is a minimal controller-runtime controller, built only to
// compare binary size and dependencies with a kube controller. It owns a
// Service for each Deployment.
package main

import (
	"context"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	ctrl "sigs.k8s.io/controller-runtime"
	"sigs.k8s.io/controller-runtime/pkg/client"
)

type reconciler struct{ client.Client }

func (r *reconciler) Reconcile(ctx context.Context, req ctrl.Request) (ctrl.Result, error) {
	var d appsv1.Deployment
	if err := r.Get(ctx, req.NamespacedName, &d); err != nil {
		return ctrl.Result{}, client.IgnoreNotFound(err)
	}
	svc := &corev1.Service{ObjectMeta: metav1.ObjectMeta{Name: d.Name, Namespace: d.Namespace}}
	_, err := ctrl.CreateOrUpdate(ctx, r.Client, svc, func() error {
		if d.Spec.Selector != nil {
			svc.Spec.Selector = d.Spec.Selector.MatchLabels
		}
		svc.Spec.Ports = []corev1.ServicePort{{Name: "http", Port: 80}}
		return ctrl.SetControllerReference(&d, svc, r.Scheme())
	})
	return ctrl.Result{}, err
}

func main() {
	mgr, err := ctrl.NewManager(ctrl.GetConfigOrDie(), ctrl.Options{})
	if err != nil {
		panic(err)
	}
	if err := ctrl.NewControllerManagedBy(mgr).For(&appsv1.Deployment{}).Owns(&corev1.Service{}).Complete(&reconciler{mgr.GetClient()}); err != nil {
		panic(err)
	}
	if err := mgr.Start(ctrl.SetupSignalHandler()); err != nil {
		panic(err)
	}
}
