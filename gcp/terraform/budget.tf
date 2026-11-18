# A monthly budget for every charge in this project, after credits.
#
# Cloud Billing emails the billing account administrators and users at
# 50% and 90% of actual spend, and when the month's forecast reaches
# 100%. Spend reaches a budget hours after the usage, so an alert is a
# backstop, not a real-time guard.
#
# The deploy account holds roles/billing.costsManager on the billing
# account so wehadababyitsaboy can manage its own budget, which means it
# can also change or delete this one.
#
# The currency has to be the billing account's currency. This stack
# uses USD.

# Not in google_project_service.services: data.google_project.project
# depends on that set, and a change there replaces the billing IAM members.
resource "google_project_service" "billing_budgets" {
  project            = var.project_id
  service            = "billingbudgets.googleapis.com"
  disable_on_destroy = false
}

resource "google_billing_budget" "project" {
  billing_account = data.google_project.project.billing_account
  display_name    = "${var.project_id} monthly"

  budget_filter {
    projects               = ["projects/${data.google_project.project.number}"]
    credit_types_treatment = "INCLUDE_ALL_CREDITS"
    calendar_period        = "MONTH"
  }

  amount {
    specified_amount {
      currency_code = "USD"
      units         = tostring(var.monthly_budget_usd)
    }
  }

  threshold_rules {
    threshold_percent = 0.5
  }

  threshold_rules {
    threshold_percent = 0.9
  }

  threshold_rules {
    threshold_percent = 1.0
    spend_basis       = "FORECASTED_SPEND"
  }

  depends_on = [google_project_service.billing_budgets]

  lifecycle {
    precondition {
      condition     = data.google_project.project.billing_account != ""
      error_message = "The project has no billing account, so it cannot have a budget."
    }
  }
}
