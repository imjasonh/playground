# A $1 monthly budget for the usage-log bucket.
#
# A budget filters by one label. The logs bucket carries whbiab=logs,
# and this budget counts Cloud Storage charges with that label, in this
# project, after credits. When the month's charges exceed $1, Cloud Billing
# emails the billing account administrators and users, and the project
# owners. It checks a few times a day.
#
# The currency has to be the billing account's currency. This stack
# uses USD.
#
# Creating the budget needs roles/billing.costsManager on the billing
# account, and a later plan needs roles/billing.viewer. gcp/terraform
# grants those to the deploy and plan accounts. Apply that stack before
# this one.

locals {
  logs_cost_label = {
    whbiab = "logs"
  }
}

data "google_project" "project" {
  project_id = var.project_id
}

resource "google_project_service" "billing_budgets" {
  service            = "billingbudgets.googleapis.com"
  disable_on_destroy = false
}

resource "google_billing_budget" "logs" {
  billing_account = data.google_project.project.billing_account
  display_name    = "wehadababyitsaboy usage logs"

  budget_filter {
    projects = ["projects/${data.google_project.project.number}"]
    # Cloud Storage. The catalog id is stable.
    services               = ["services/95FF-2EF5-5EA1"]
    labels                 = local.logs_cost_label
    calendar_period        = "MONTH"
    credit_types_treatment = "INCLUDE_ALL_CREDITS"
  }

  amount {
    specified_amount {
      currency_code = "USD"
      units         = "1"
    }
  }

  # Exceeding 1.0 means the month's charges are over $1.
  threshold_rules {
    threshold_percent = 1.0
    spend_basis       = "CURRENT_SPEND"
  }

  all_updates_rule {
    monitoring_notification_channels = []
    enable_project_level_recipients  = true
  }

  depends_on = [
    google_project_service.billing_budgets,
    google_storage_bucket.logs,
  ]

  lifecycle {
    precondition {
      condition     = data.google_project.project.billing_account != ""
      error_message = "The project has no billing account, so a $1 usage-log budget cannot be created."
    }
  }
}
