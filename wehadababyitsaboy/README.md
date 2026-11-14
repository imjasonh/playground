# wehadababyitsaboy

Usage tracking for CLIs and web pages with nothing but an empty Cloud
Storage bucket. A client requests a URL in the bucket, the request fails,
and Cloud Storage writes it to the bucket's hourly usage log.
`report.sh` counts the requests that carry `?bob=wehadababyitsaboy`.

## Record a request

Request this URL from any HTTP client:

```
https://storage.googleapis.com/wehadababyitsaboy/CLIENT/ARGS?bob=wehadababyitsaboy
```

Replace the following:

- `CLIENT`: the name of the CLI or page, such as `mycli`.
- `ARGS`: the subcommand, arguments, and flags, separated by dots, such as
  `deploy.--dry-run`. Percent-encode anything that isn't safe in a URL path.

From a shell script, send the request in the background so that it never
slows the command:

```bash
curl -s -o /dev/null --max-time 2 \
  "https://storage.googleapis.com/wehadababyitsaboy/mycli/deploy.--dry-run?bob=wehadababyitsaboy" &
```

From a web page, use an image. The request fails, so hide the broken
image:

```html
<img src="https://storage.googleapis.com/wehadababyitsaboy/mypage/home?bob=wehadababyitsaboy"
     alt="" width="1" height="1" hidden>
```

Every request returns `403 Forbidden`. The bucket is empty and nobody can
read it, so no request returns data.

Use the HTTPS URL, not a `gs://` URI. A `gs://` URI has no query string,
and `gcloud storage` treats `?` as a wildcard, so it lists the bucket
instead of reading one object.

## Read the counts

Usage logs arrive about 15 minutes after the end of each hour, and Cloud
Storage can take up to six hours. To count requests by client and
arguments over the last seven days, run the following:

```bash
./report.sh 7
```

`report.sh` needs `bq` and `gcloud`, signed in to the project that owns
the buckets. It reads the CSVs in place through a temporary BigQuery
external table, and it counts a request that appears twice in the logs
once. Each row has the client, the arguments, the number of requests, the
number of client IP addresses, and the time of the last request.

For anything else, read the CSVs in `gs://wehadababyitsaboy-logs/`. Each
row also has the referrer and the User-Agent. For the format, see
[Usage logs and storage logs](https://cloud.google.com/storage/docs/access-logs#format).

## How it works

`terraform/` creates two buckets in `us-central1`:

- `wehadababyitsaboy`, the empty bucket that clients request. Public access
  prevention is on, so a request from anyone fails.
- `wehadababyitsaboy-logs`, where Cloud Storage writes the usage logs of the
  first bucket. Only `cloud-storage-analytics@google.com` can write to it.

Cloud Storage writes a usage log row for every request, including failed
and anonymous ones. The row has the full URI with its query string. The
logs can't be filtered as they're written, so a request without
`?bob=wehadababyitsaboy` costs a row too. `report.sh` leaves it out.

`bob=wehadababyitsaboy` is in every page and script that uses it, so it
isn't a secret. It keeps scanners and crawlers that request random paths
out of the counts. It doesn't stop someone from sending fake requests on
purpose.

Cloud Audit Logs and a Logs Router sink can't do this job:

- Audit logs don't record requests that `allUsers` access serves, so a
  public bucket logs nothing. An `<img>` request carries no credentials.
- Audit logs don't record query strings, except for parameters named
  `x-goog-custom-audit-KEY`.
- Data Access audit logs for Cloud Storage turn on for the whole project,
  so they would also log every read of every other bucket.

## Cost

Usage logs cost nothing to write. You pay to store them, at about 300
bytes for each request, so a million requests is about 300 MB. Cloud
Storage doesn't charge for requests that fail with `403`. A `report.sh`
query is billed by the bytes that it reads, within the free first TB each
month.

The logs bucket is labeled `whbiab=logs`. A Cloud Billing budget of $1
per month counts Cloud Storage charges with that label in this project,
after credits. When those charges exceed $1, Cloud Billing emails the
billing account administrators and users, and the project's owners. It
checks a few times a day. Traffic from the empty bucket, including the
403 responses, is not part of this budget. The billing account must use
USD.

## Deploy

`deploy-gcp.yml` applies `terraform/` on pushes to `main` that change this
directory, with the shared deploy account from `gcp/terraform`. A pull
request comments the plan. Apply `gcp/terraform` first, with a
principal that can set the billing account's IAM policy, so the deploy
account can create the budget and the plan account can read it. Then
apply this stack. To apply by hand, run the following:

```bash
cd terraform
tofu init -backend-config="bucket=STATE_BUCKET"
# User credentials need a quota project for the Billing Budgets API.
# The deploy service account does not.
export GOOGLE_BILLING_PROJECT=PROJECT_ID USER_PROJECT_OVERRIDE=true
tofu apply -var project_id=PROJECT_ID
```

Replace the following:

- `STATE_BUCKET`: the Terraform state bucket that the other app stacks use.
- `PROJECT_ID`: the Google Cloud project.
