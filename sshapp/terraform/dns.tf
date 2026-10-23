resource "google_dns_managed_zone" "apps" {
  count = local.create_dns_zone ? 1 : 0

  name        = replace(var.domain, ".", "-")
  dns_name    = "${trimsuffix(var.domain, ".")}."
  description = "Public DNS for sshapp apps (<app>.${var.domain})."
  visibility  = "public"

  dnssec_config {
    state = "on"
  }

  depends_on = [google_project_service.services]
}

data "google_dns_managed_zone" "existing" {
  count = local.use_existing_zone ? 1 : 0
  name  = var.dns_zone_name
}
