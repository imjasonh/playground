#!/usr/bin/env bash
# Count the requests that carry ?bob=wehadababyitsaboy, by client and
# arguments, from the usage logs of the last DAYS days.
#
# Usage: report.sh [DAYS]
#
# Env:
#   PROJECT      project that runs the BigQuery job. Default: gcloud's project.
#   LOGS_BUCKET  bucket that holds the usage logs. Default: wehadababyitsaboy-logs.
#
# The query reads the CSVs in place through a temporary external table, so
# it needs no dataset. Every column is a string, which also lets the CSV
# header rows through; the bob filter drops them.
set -euo pipefail

days=${1:-7}
if [[ ! "$days" =~ ^[0-9]+$ ]]; then
  echo "usage: report.sh [DAYS]" >&2
  exit 2
fi
logs=${LOGS_BUCKET:-wehadababyitsaboy-logs}
project=${PROJECT:-$(gcloud config get project 2>/dev/null)}

columns=(
  time_micros c_ip c_ip_type c_ip_region cs_method cs_uri sc_status
  cs_bytes sc_bytes time_taken_micros cs_host cs_referer cs_user_agent
  s_request_id cs_operation cs_bucket cs_object
)
schema=$(printf '%s:STRING,' "${columns[@]}")
schema=${schema%,}

bq --project_id="$project" query \
  --nouse_legacy_sql \
  --format=pretty \
  --external_table_definition="usage::${schema}@CSV=gs://${logs}/usage_usage_*" \
  "WITH hits AS (
     SELECT
       TIMESTAMP_MICROS(CAST(time_micros AS INT64)) AS time,
       SPLIT(cs_object, '/')[SAFE_OFFSET(0)] AS client,
       REGEXP_EXTRACT(cs_object, r'^[^/]*/(.*)$') AS args,
       c_ip,
       s_request_id
     FROM usage
     WHERE REGEXP_CONTAINS(cs_uri, r'[?&]bob=wehadababyitsaboy(&|$)')
   )
   SELECT
     client,
     args,
     COUNT(DISTINCT s_request_id) AS requests,
     COUNT(DISTINCT c_ip) AS ips,
     MAX(time) AS last_seen
   FROM hits
   WHERE time >= TIMESTAMP_SUB(CURRENT_TIMESTAMP(), INTERVAL ${days} DAY)
   GROUP BY client, args
   ORDER BY requests DESC"
