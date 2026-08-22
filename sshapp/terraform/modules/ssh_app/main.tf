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

resource "kubernetes_deployment_v1" "app" {
  metadata {
    name      = var.name
    namespace = var.namespace
    labels    = local.labels
  }

  spec {
    replicas = local.app_replicas

    strategy {
      type = var.deployment_strategy

      dynamic "rolling_update" {
        for_each = var.deployment_strategy == "RollingUpdate" ? [1] : []
        content {
          max_unavailable = "0"
          max_surge       = "1"
        }
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
        automount_service_account_token  = false
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
    ignore_changes = [spec[0].replicas]
  }
}

resource "kubernetes_service_v1" "app" {
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
