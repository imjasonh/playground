terraform {
  required_providers {
    google = {
      source = "hashicorp/google"
    }
    kubernetes = {
      source = "hashicorp/kubernetes"
    }
    ko = {
      source = "ko-build/ko"
    }
    tls = {
      source = "hashicorp/tls"
    }
  }
}

locals {
  labels = merge(
    {
      "app.kubernetes.io/name"       = var.name
      "app.kubernetes.io/component"  = "ssh-app"
      "app.kubernetes.io/managed-by" = "terraform"
    },
    var.labels,
  )

  activator_labels = merge(local.labels, {
    "app.kubernetes.io/name"      = "${var.name}-activator"
    "app.kubernetes.io/component" = "activator"
  })

  fqdn = "${var.name}.${trimsuffix(var.domain, ".")}"

  # Public Service selects the activator when scale-to-zero is on; otherwise the app.
  public_selector = var.scale_to_zero ? {
    "app.kubernetes.io/name" = "${var.name}-activator"
    } : {
    "app.kubernetes.io/name" = var.name
  }

  app_replicas = var.scale_to_zero ? 0 : var.replicas
}

resource "tls_private_key" "host" {
  algorithm = "ED25519"
}

resource "ko_build" "app" {
  importpath  = var.importpath
  working_dir = var.working_dir
  platforms   = ["linux/amd64"]
  sbom        = "none"
  tags        = [var.name]
}

resource "ko_build" "activator" {
  count = var.scale_to_zero ? 1 : 0

  importpath  = var.activator_importpath
  working_dir = var.working_dir
  platforms   = ["linux/amd64"]
  sbom        = "none"
  tags        = ["${var.name}-activator"]
}

resource "kubernetes_secret_v1" "host_key" {
  metadata {
    name      = "${var.name}-ssh-host-key"
    namespace = var.namespace
    labels    = local.labels
  }

  type = "Opaque"

  data = {
    host_ed25519 = tls_private_key.host.private_key_openssh
  }
}

resource "kubernetes_service_account_v1" "activator" {
  count = var.scale_to_zero ? 1 : 0

  metadata {
    name      = "${var.name}-activator"
    namespace = var.namespace
    labels    = local.activator_labels
  }
}

resource "kubernetes_role_v1" "activator" {
  count = var.scale_to_zero ? 1 : 0

  metadata {
    name      = "${var.name}-activator"
    namespace = var.namespace
    labels    = local.activator_labels
  }

  rule {
    api_groups = ["apps"]
    resources  = ["deployments", "deployments/scale"]
    verbs      = ["get", "patch", "update"]
  }

  rule {
    api_groups = [""]
    resources  = ["endpoints", "services"]
    verbs      = ["get", "list", "watch"]
  }
}

resource "kubernetes_role_binding_v1" "activator" {
  count = var.scale_to_zero ? 1 : 0

  metadata {
    name      = "${var.name}-activator"
    namespace = var.namespace
    labels    = local.activator_labels
  }

  role_ref {
    api_group = "rbac.authorization.k8s.io"
    kind      = "Role"
    name      = kubernetes_role_v1.activator[0].metadata[0].name
  }

  subject {
    kind      = "ServiceAccount"
    name      = kubernetes_service_account_v1.activator[0].metadata[0].name
    namespace = var.namespace
  }
}

resource "kubernetes_deployment_v1" "app" {
  metadata {
    name      = var.name
    namespace = var.namespace
    labels    = local.labels
  }

  spec {
    replicas = local.app_replicas

    strategy {
      type = "RollingUpdate"
      rolling_update {
        # Keep old pod until the new one is ready so in-flight SSH sessions
        # drain instead of hard-cutting on upgrade when replicas > 0.
        max_unavailable = "0"
        max_surge       = "1"
      }
    }

    selector {
      match_labels = {
        "app.kubernetes.io/name" = var.name
      }
    }

    template {
      metadata {
        labels = local.labels
        annotations = {
          "sshapp.playground/image" = ko_build.app.image_ref
        }
      }

      spec {
        automount_service_account_token = false
        termination_grace_period_seconds = 45

        security_context {
          run_as_non_root = true
          seccomp_profile {
            type = "RuntimeDefault"
          }
        }

        container {
          name  = "ssh"
          image = ko_build.app.image_ref

          port {
            name           = "ssh"
            container_port = var.container_port
            protocol       = "TCP"
          }

          env {
            name  = "SSHAPP_ADDR"
            value = ":${var.container_port}"
          }

          env {
            name  = "SSHAPP_HOST_KEY_PATH"
            value = "/var/run/ssh/host_ed25519"
          }

          resources {
            requests = {
              cpu               = "250m"
              memory            = "512Mi"
              ephemeral-storage = "100Mi"
            }
            limits = {
              cpu               = "500m"
              memory            = "512Mi"
              ephemeral-storage = "200Mi"
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

          liveness_probe {
            tcp_socket {
              port = var.container_port
            }
            initial_delay_seconds = 5
            period_seconds        = 20
          }

          readiness_probe {
            tcp_socket {
              port = var.container_port
            }
            initial_delay_seconds = 2
            period_seconds        = 5
          }
        }

        volume {
          name = "tmp"
          empty_dir {}
        }

        volume {
          name = "ssh-host-key"
          secret {
            secret_name = kubernetes_secret_v1.host_key.metadata[0].name
            items {
              key  = "host_ed25519"
              path = "host_ed25519"
            }
          }
        }
      }
    }
  }

  lifecycle {
    # Activator owns replica count when scale-to-zero is enabled.
    ignore_changes = [spec[0].replicas]
  }
}

resource "kubernetes_deployment_v1" "activator" {
  count = var.scale_to_zero ? 1 : 0

  metadata {
    name      = "${var.name}-activator"
    namespace = var.namespace
    labels    = local.activator_labels
  }

  spec {
    replicas = 1

    selector {
      match_labels = {
        "app.kubernetes.io/name" = "${var.name}-activator"
      }
    }

    template {
      metadata {
        labels = local.activator_labels
        annotations = {
          "sshapp.playground/image" = ko_build.activator[0].image_ref
        }
      }

      spec {
        service_account_name = kubernetes_service_account_v1.activator[0].metadata[0].name

        security_context {
          run_as_non_root = true
          seccomp_profile {
            type = "RuntimeDefault"
          }
        }

        container {
          name  = "activator"
          image = ko_build.activator[0].image_ref

          port {
            name           = "ssh"
            container_port = var.container_port
            protocol       = "TCP"
          }

          env {
            name  = "SSHAPP_LISTEN"
            value = ":${var.container_port}"
          }

          env {
            name  = "SSHAPP_NAMESPACE"
            value = var.namespace
          }

          env {
            name  = "SSHAPP_APP"
            value = var.name
          }

          env {
            name  = "SSHAPP_BACKEND_PORT"
            value = tostring(var.container_port)
          }

          env {
            name  = "SSHAPP_WARM_REPLICAS"
            value = tostring(var.replicas)
          }

          env {
            name  = "SSHAPP_IDLE_AFTER"
            value = var.idle_after
          }

          resources {
            requests = {
              cpu               = "100m"
              memory            = "256Mi"
              ephemeral-storage = "50Mi"
            }
            limits = {
              cpu               = "250m"
              memory            = "256Mi"
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

          readiness_probe {
            tcp_socket {
              port = var.container_port
            }
            initial_delay_seconds = 1
            period_seconds        = 5
          }
        }

        volume {
          name = "tmp"
          empty_dir {}
        }
      }
    }
  }

  depends_on = [kubernetes_role_binding_v1.activator]
}

# Internal ClusterIP so the activator can find ready app pods by Endpoints.
resource "kubernetes_service_v1" "app_internal" {
  count = var.scale_to_zero ? 1 : 0

  metadata {
    name      = var.name
    namespace = var.namespace
    labels    = local.labels
  }

  spec {
    type = "ClusterIP"

    selector = {
      "app.kubernetes.io/name" = var.name
    }

    port {
      name        = "ssh"
      port        = var.container_port
      target_port = var.container_port
      protocol    = "TCP"
    }
  }
}

resource "kubernetes_service_v1" "public" {
  metadata {
    name      = var.scale_to_zero ? "${var.name}-ssh" : var.name
    namespace = var.namespace
    labels    = var.scale_to_zero ? local.activator_labels : local.labels
    annotations = {
      "cloud.google.com/neg" = jsonencode({ ingress = false })
    }
  }

  spec {
    type                        = "LoadBalancer"
    external_traffic_policy     = "Local"
    load_balancer_source_ranges = var.ssh_source_ranges

    selector = local.public_selector

    port {
      name        = "ssh"
      port        = 22
      target_port = var.container_port
      protocol    = "TCP"
    }
  }
}

resource "google_dns_record_set" "app" {
  name         = "${local.fqdn}."
  managed_zone = var.dns_managed_zone
  type         = "A"
  ttl          = 60

  rrdatas = [
    one([
      for ingress in kubernetes_service_v1.public.status[0].load_balancer[0].ingress : ingress.ip
      if ingress.ip != null && ingress.ip != ""
    ])
  ]

  depends_on = [kubernetes_service_v1.public]
}
