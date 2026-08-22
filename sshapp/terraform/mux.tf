locals {
  mux_labels = {
    "app.kubernetes.io/name"       = "ssh-mux"
    "app.kubernetes.io/component"  = "mux"
    "app.kubernetes.io/part-of"    = var.name
    "app.kubernetes.io/managed-by" = "terraform"
  }

  mux_app_config = jsonencode({
    for name, app in var.apps : name => {
      replicas      = app.replicas
      scale_to_zero = app.scale_to_zero
    }
  })
}

resource "tls_private_key" "mux_host" {
  algorithm = "ED25519"
}

resource "ko_build" "mux" {
  importpath  = "github.com/imjasonh/playground/sshapp/apps/mux"
  working_dir = abspath("${path.module}/..")
  platforms   = ["linux/amd64"]
  sbom        = "none"
  tags        = ["mux"]
}

resource "kubernetes_secret_v1" "mux_host_key" {
  metadata {
    name      = "ssh-mux-host-key"
    namespace = kubernetes_namespace.apps.metadata[0].name
    labels    = local.mux_labels
  }

  type = "Opaque"

  data = {
    host_ed25519 = tls_private_key.mux_host.private_key_openssh
  }
}

resource "kubernetes_service_account_v1" "mux" {
  metadata {
    name      = "ssh-mux"
    namespace = kubernetes_namespace.apps.metadata[0].name
    labels    = local.mux_labels
  }
}

resource "kubernetes_role_v1" "mux" {
  metadata {
    name      = "ssh-mux"
    namespace = kubernetes_namespace.apps.metadata[0].name
    labels    = local.mux_labels
  }

  rule {
    api_groups = ["apps"]
    resources  = ["deployments", "deployments/scale"]
    verbs      = ["get", "patch", "update", "list", "watch"]
  }

  rule {
    api_groups = [""]
    resources  = ["endpoints", "services"]
    verbs      = ["get", "list", "watch"]
  }
}

resource "kubernetes_role_binding_v1" "mux" {
  metadata {
    name      = "ssh-mux"
    namespace = kubernetes_namespace.apps.metadata[0].name
    labels    = local.mux_labels
  }

  role_ref {
    api_group = "rbac.authorization.k8s.io"
    kind      = "Role"
    name      = kubernetes_role_v1.mux.metadata[0].name
  }

  subject {
    kind      = "ServiceAccount"
    name      = kubernetes_service_account_v1.mux.metadata[0].name
    namespace = kubernetes_namespace.apps.metadata[0].name
  }
}

resource "kubernetes_deployment_v1" "mux" {
  metadata {
    name      = "ssh-mux"
    namespace = kubernetes_namespace.apps.metadata[0].name
    labels    = local.mux_labels
  }

  spec {
    replicas = 1

    selector {
      match_labels = {
        "app.kubernetes.io/name" = "ssh-mux"
      }
    }

    template {
      metadata {
        labels = local.mux_labels
        annotations = {
          "sshapp.playground/image" = ko_build.mux.image_ref
        }
      }

      spec {
        service_account_name = kubernetes_service_account_v1.mux.metadata[0].name

        security_context {
          run_as_non_root = true
          seccomp_profile {
            type = "RuntimeDefault"
          }
        }

        container {
          name  = "mux"
          image = ko_build.mux.image_ref

          port {
            name           = "ssh"
            container_port = 2222
            protocol       = "TCP"
          }

          env {
            name  = "SSHAPP_LISTEN"
            value = ":2222"
          }

          env {
            name  = "SSHAPP_NAMESPACE"
            value = kubernetes_namespace.apps.metadata[0].name
          }

          env {
            name  = "SSHAPP_APP_CONFIG"
            value = local.mux_app_config
          }

          env {
            name  = "SSHAPP_IDLE_AFTER"
            value = var.mux_idle_after
          }

          env {
            name  = "SSHAPP_HOST_KEY_PATH"
            value = "/var/run/ssh/host_ed25519"
          }

          resources {
            requests = {
              cpu               = "100m"
              memory            = "256Mi"
              ephemeral-storage = "50Mi"
            }
            limits = {
              cpu               = "500m"
              memory            = "512Mi"
              ephemeral-storage = "100Mi"
            }
          }

          security_context {
            allow_privilege_escalation = false
            read_only_root_filesystem  = true
            run_as_non_root            = true
            capabilities {
              drop = ["ALL"]
            }
          }

          volume_mount {
            name       = "tmp"
            mount_path = "/tmp"
          }

          volume_mount {
            name       = "ssh-host-key"
            mount_path = "/var/run/ssh"
            read_only  = true
          }

          readiness_probe {
            tcp_socket {
              port = 2222
            }
            initial_delay_seconds = 1
            period_seconds        = 5
          }

          liveness_probe {
            tcp_socket {
              port = 2222
            }
            initial_delay_seconds = 5
            period_seconds        = 20
          }
        }

        volume {
          name = "tmp"
          empty_dir {}
        }

        volume {
          name = "ssh-host-key"
          secret {
            secret_name = kubernetes_secret_v1.mux_host_key.metadata[0].name
            items {
              key  = "host_ed25519"
              path = "host_ed25519"
            }
          }
        }
      }
    }
  }

  depends_on = [
    kubernetes_role_binding_v1.mux,
    module.app,
  ]
}

# Single external LoadBalancer for every SSH app.
resource "kubernetes_service_v1" "mux" {
  metadata {
    name      = "ssh-mux"
    namespace = kubernetes_namespace.apps.metadata[0].name
    labels    = local.mux_labels
    annotations = {
      "cloud.google.com/neg" = jsonencode({ ingress = false })
    }
  }

  spec {
    type                        = "LoadBalancer"
    external_traffic_policy     = "Local"
    load_balancer_source_ranges = local.ssh_source_ranges

    selector = {
      "app.kubernetes.io/name" = "ssh-mux"
    }

    port {
      name        = "ssh"
      port        = 22
      target_port = 2222
      protocol    = "TCP"
    }
  }
}

resource "google_dns_record_set" "mux" {
  name         = "ssh.${trimsuffix(var.domain, ".")}."
  managed_zone = local.dns_zone_name
  type         = "A"
  ttl          = 60

  rrdatas = [
    one([
      for ingress in kubernetes_service_v1.mux.status[0].load_balancer[0].ingress : ingress.ip
      if ingress.ip != null && ingress.ip != ""
    ])
  ]

  depends_on = [kubernetes_service_v1.mux]
}

# Wildcard so any <app>.domain hits the mux IP even without a per-app CNAME.
resource "google_dns_record_set" "mux_wildcard" {
  name         = "*.${trimsuffix(var.domain, ".")}."
  managed_zone = local.dns_zone_name
  type         = "A"
  ttl          = 60

  rrdatas = google_dns_record_set.mux.rrdatas
}
