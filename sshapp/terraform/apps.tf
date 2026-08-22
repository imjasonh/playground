module "app" {
  source   = "./modules/ssh_app"
  for_each = var.apps

  name                = each.key
  namespace           = kubernetes_namespace.apps.metadata[0].name
  importpath          = each.value.importpath
  working_dir         = abspath("${path.module}/..")
  replicas            = each.value.replicas
  scale_to_zero       = each.value.scale_to_zero
  deployment_strategy = each.value.deployment_strategy

  labels = {
    "app.kubernetes.io/part-of" = var.name
  }

  depends_on = [
    google_artifact_registry_repository_iam_member.node_reader,
    google_container_cluster.sshapp,
  ]
}
