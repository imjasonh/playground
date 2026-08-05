locals {
  sshcloud_vm_log_filter      = <<-EOT
    resource.type="gce_instance"
    AND labels."compute.googleapis.com/resource_name"=~"^${local.prefix}-(gateway|orchestrator|snapshot|agent)"
  EOT
  alert_notification_channels = google_monitoring_notification_channel.email[*].name
}

resource "google_logging_project_bucket_config" "platform" {
  project        = var.project_id
  location       = "global"
  bucket_id      = "${local.prefix}-platform"
  retention_days = 30
  description    = "sshcloud platform and host diagnostics; never SSH channel payloads"
  depends_on     = [module.project_services]
}

resource "google_logging_project_bucket_config" "app" {
  project        = var.project_id
  location       = "global"
  bucket_id      = "${local.prefix}-app"
  retention_days = 7
  description    = "Bounded app-owned serial-console logs and strict app telemetry"
  depends_on     = [module.project_services]
}

resource "google_logging_project_sink" "platform" {
  name                   = "${local.prefix}-platform"
  project                = var.project_id
  destination            = "logging.googleapis.com/${google_logging_project_bucket_config.platform.name}"
  filter                 = "${local.sshcloud_vm_log_filter}\nAND NOT jsonPayload.log_type=\"app\""
  unique_writer_identity = true
}

resource "google_logging_project_sink" "app" {
  name                   = "${local.prefix}-app"
  project                = var.project_id
  destination            = "logging.googleapis.com/${google_logging_project_bucket_config.app.name}"
  filter                 = "${local.sshcloud_vm_log_filter}\nAND jsonPayload.log_type=\"app\""
  unique_writer_identity = true
}

resource "google_project_iam_member" "platform_sink" {
  project = var.project_id
  role    = "roles/logging.bucketWriter"
  member  = google_logging_project_sink.platform.writer_identity

  condition {
    title       = "${local.prefix}-platform-log-bucket"
    description = "Limit the platform sink writer to its dedicated log bucket"
    expression  = "resource.name == \"${google_logging_project_bucket_config.platform.name}\""
  }
}

resource "google_project_iam_member" "app_sink" {
  project = var.project_id
  role    = "roles/logging.bucketWriter"
  member  = google_logging_project_sink.app.writer_identity

  condition {
    title       = "${local.prefix}-app-log-bucket"
    description = "Limit the app sink writer to its seven-day log bucket"
    expression  = "resource.name == \"${google_logging_project_bucket_config.app.name}\""
  }
}

# Keep sshcloud records out of _Default after their dedicated sinks accept
# them. _Required remains untouched.
resource "google_logging_project_exclusion" "sshcloud_default" {
  project     = var.project_id
  name        = "${local.prefix}-dedicated-buckets"
  description = "Avoid duplicate retention after platform/app bucket routing"
  filter      = local.sshcloud_vm_log_filter
  depends_on = [
    google_project_iam_member.platform_sink,
    google_project_iam_member.app_sink,
  ]
}

resource "google_logging_metric" "platform_errors" {
  project     = var.project_id
  name        = "${local.prefix}-platform-errors"
  description = "Structured sshcloud platform errors; app records are excluded"
  filter      = "${local.sshcloud_vm_log_filter}\nAND jsonPayload.log_type=\"platform\"\nAND severity>=ERROR"

  metric_descriptor {
    metric_kind = "DELTA"
    value_type  = "INT64"
    unit        = "1"
  }
  depends_on = [module.project_services]
}

resource "google_monitoring_notification_channel" "email" {
  count        = var.notification_email == null ? 0 : 1
  project      = var.project_id
  display_name = "${local.prefix} operator email"
  type         = "email"
  labels = {
    email_address = var.notification_email
  }
  depends_on = [module.project_services]
}

resource "google_monitoring_alert_policy" "ops_agent_absent" {
  project      = var.project_id
  display_name = "${local.prefix}: Ops Agent metrics absent"
  combiner     = "OR"

  conditions {
    display_name = "No sshcloud scrape heartbeat for 10 minutes"
    condition_threshold {
      filter                    = "resource.type = \"prometheus_target\" AND metric.type = \"prometheus.googleapis.com/sshcloud_up/gauge\""
      comparison                = "COMPARISON_LT"
      threshold_value           = 0.5
      duration                  = "600s"
      evaluation_missing_data   = "EVALUATION_MISSING_DATA_ACTIVE"
      disable_metric_validation = true
      aggregations {
        alignment_period   = "60s"
        per_series_aligner = "ALIGN_MEAN"
      }
    }
  }

  notification_channels = local.alert_notification_channels
  alert_strategy {
    auto_close = "1800s"
  }
  depends_on = [module.project_services]
}

resource "google_monitoring_alert_policy" "disk_high" {
  project      = var.project_id
  display_name = "${local.prefix}: host disk above 90%"
  combiner     = "OR"

  conditions {
    display_name = "Persistent disk percent used"
    condition_threshold {
      filter          = "resource.type = \"gce_instance\" AND metric.type = \"agent.googleapis.com/disk/percent_used\" AND metric.label.\"state\" = \"used\""
      comparison      = "COMPARISON_GT"
      threshold_value = 90
      duration        = "300s"
      aggregations {
        alignment_period     = "60s"
        per_series_aligner   = "ALIGN_MEAN"
        cross_series_reducer = "REDUCE_MAX"
        group_by_fields      = ["resource.label.instance_id"]
      }
    }
  }

  notification_channels = local.alert_notification_channels
  alert_strategy {
    auto_close = "1800s"
  }
  depends_on = [module.project_services]
}

resource "google_monitoring_alert_policy" "app_log_drops" {
  project      = var.project_id
  display_name = "${local.prefix}: app console bytes dropped"
  combiner     = "OR"

  conditions {
    display_name = "Nonblocking host console guard dropped bytes"
    condition_threshold {
      filter                    = "resource.type = \"prometheus_target\" AND metric.type = \"prometheus.googleapis.com/sshcloud_app_log_bytes_total/counter\" AND metric.label.\"result\" = \"dropped\""
      comparison                = "COMPARISON_GT"
      threshold_value           = 0
      duration                  = "0s"
      disable_metric_validation = true
      aggregations {
        alignment_period     = "300s"
        per_series_aligner   = "ALIGN_DELTA"
        cross_series_reducer = "REDUCE_SUM"
      }
    }
  }

  notification_channels = local.alert_notification_channels
  alert_strategy {
    auto_close = "1800s"
  }
  depends_on = [module.project_services]
}

resource "google_monitoring_alert_policy" "platform_errors" {
  project      = var.project_id
  display_name = "${local.prefix}: platform errors"
  combiner     = "OR"

  conditions {
    display_name = "Structured platform error log count"
    condition_threshold {
      filter          = "resource.type = \"gce_instance\" AND metric.type = \"logging.googleapis.com/user/${google_logging_metric.platform_errors.name}\""
      comparison      = "COMPARISON_GT"
      threshold_value = 0
      duration        = "0s"
      aggregations {
        alignment_period     = "300s"
        per_series_aligner   = "ALIGN_DELTA"
        cross_series_reducer = "REDUCE_SUM"
      }
    }
  }

  notification_channels = local.alert_notification_channels
  alert_strategy {
    auto_close = "1800s"
  }
}

resource "google_monitoring_dashboard" "sshcloud" {
  project = var.project_id
  dashboard_json = jsonencode({
    displayName = "${local.prefix} operations"
    gridLayout = {
      columns = 2
      widgets = [
        {
          title = "Host CPU utilization"
          xyChart = {
            dataSets = [{
              plotType = "LINE"
              timeSeriesQuery = {
                timeSeriesFilter = {
                  filter = "resource.type=\"gce_instance\" metric.type=\"agent.googleapis.com/cpu/utilization\""
                  aggregation = {
                    alignmentPeriod  = "60s"
                    perSeriesAligner = "ALIGN_MEAN"
                  }
                }
              }
            }]
            yAxis = { label = "utilization", scale = "LINEAR" }
          }
        },
        {
          title = "Host disk percent used"
          xyChart = {
            dataSets = [{
              plotType = "LINE"
              timeSeriesQuery = {
                timeSeriesFilter = {
                  filter = "resource.type=\"gce_instance\" metric.type=\"agent.googleapis.com/disk/percent_used\" metric.label.state=\"used\""
                  aggregation = {
                    alignmentPeriod  = "60s"
                    perSeriesAligner = "ALIGN_MEAN"
                  }
                }
              }
            }]
            yAxis = { label = "percent", scale = "LINEAR" }
          }
        },
        {
          title = "App console bytes accepted/dropped"
          xyChart = {
            dataSets = [{
              plotType = "STACKED_AREA"
              timeSeriesQuery = {
                timeSeriesFilter = {
                  filter = "resource.type=\"prometheus_target\" metric.type=\"prometheus.googleapis.com/sshcloud_app_log_bytes_total/counter\""
                  aggregation = {
                    alignmentPeriod  = "300s"
                    perSeriesAligner = "ALIGN_DELTA"
                  }
                }
              }
            }]
            yAxis = { label = "bytes / 5m", scale = "LINEAR" }
          }
        },
        {
          title = "Lifecycle failures"
          xyChart = {
            dataSets = [{
              plotType = "STACKED_BAR"
              timeSeriesQuery = {
                timeSeriesFilter = {
                  filter = "resource.type=\"prometheus_target\" metric.type=\"prometheus.googleapis.com/sshcloud_lifecycle_operations_total/counter\" metric.label.outcome=\"failure\""
                  aggregation = {
                    alignmentPeriod  = "300s"
                    perSeriesAligner = "ALIGN_DELTA"
                  }
                }
              }
            }]
            yAxis = { label = "operations / 5m", scale = "LINEAR" }
          }
        },
      ]
    }
  })
  depends_on = [module.project_services]
}

resource "google_billing_budget" "monthly" {
  count           = var.monthly_budget_usd == null ? 0 : 1
  billing_account = coalesce(var.billing_account_id, "000000-000000-000000")
  display_name    = "${local.prefix} monthly project budget"

  budget_filter {
    projects = ["projects/${data.google_project.current.number}"]
  }

  amount {
    specified_amount {
      currency_code = "USD"
      units         = tostring(coalesce(var.monthly_budget_usd, 1))
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
  }

  dynamic "all_updates_rule" {
    for_each = var.notification_email == null ? [] : [1]
    content {
      monitoring_notification_channels = local.alert_notification_channels
      disable_default_iam_recipients   = false
    }
  }

  depends_on = [module.project_services]
}
