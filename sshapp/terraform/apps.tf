module "app" {
  source   = "./modules/ssh_app"
  for_each = var.apps

  name              = each.key
  namespace         = kubernetes_namespace.apps.metadata[0].name
  importpath        = each.value.importpath
  working_dir       = abspath("${path.module}/..")
  domain            = var.domain
  dns_managed_zone  = local.dns_zone_name
  replicas          = each.value.replicas
  ssh_source_ranges = local.ssh_source_ranges

  labels = {
    "app.kubernetes.io/part-of" = var.name
  }

  depends_on = [
    google_artifact_registry_repository_iam_member.node_reader,
    google_container_cluster.sshapp,
  ]
}
