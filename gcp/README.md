# GitHub connection for Google Cloud

This stack is the Workload Identity pool that GitHub Actions uses to
deploy to this project. It is not an app. Every Cloud Run app binds its
own deploy and plan service accounts to this pool. Apply it once, before
the first app.

The pool trusts `.github/workflows/deploy-gcp.yml` in one repository.
Apply from `main` uses the `github` provider. A pull request plan uses
the `github-plan` provider. A token has to come from a GitHub environment
whose name starts with `gcp-`. An app's accounts are bound to
`gcp-<app>`, so one app's token cannot impersonate another app.

```bash
gcloud storage buckets create gs://BUCKET --location=us-central1 --uniform-bucket-level-access --public-access-prevention
gcloud storage buckets update gs://BUCKET --versioning

cd terraform
cp terraform.tfvars.example terraform.tfvars   # set project_id and github_repository
tofu init -backend-config="bucket=BUCKET"
tofu apply
```

Use the same bucket the apps use for state. This stack stores its state
under the prefix `github`. App stacks use their own prefix in that bucket.

`tofu output workload_identity_provider` and
`tofu output plan_workload_identity_provider` are the values an app
prints again as `GCP_WORKLOAD_IDENTITY_PROVIDER` and
`GCP_PLAN_WORKLOAD_IDENTITY_PROVIDER`.
