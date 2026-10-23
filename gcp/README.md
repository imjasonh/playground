# GitHub connection for Google Cloud

This stack is the Workload Identity pool and the deploy and plan
accounts that GitHub Actions uses for every app in this project. It is
not an app. Apply it once, before the first app. An app stack does not
create a pool or a GitHub account.

The pool trusts `.github/workflows/deploy-gcp.yml` in one repository.
Apply from `main` uses the `github` provider. A pull request plan uses
the `github-plan` provider. `deploy-gcp.yml` selects the GitHub
environment `gcp`, and these accounts accept only that environment. A
plan token cannot apply.

The deploy account can change app stacks and can act as any service
account in the project, so a new app does not need a binding for its
runtime account. The plan account can read the state bucket, create and delete
`.tflock` objects there (not `default.tfstate`), and push images. It
cannot delete images or read replica objects.

```bash
gcloud storage buckets create gs://BUCKET --location=us-central1 --uniform-bucket-level-access --public-access-prevention
gcloud storage buckets update gs://BUCKET --versioning

cd terraform
cp terraform.tfvars.example terraform.tfvars   # set project_id, github_repository, and state_bucket
tofu init -backend-config="bucket=BUCKET"
tofu apply
```

Use the same bucket the apps use for state. This stack stores its state
under the prefix `github`. App stacks use their own prefix in that bucket.

Create the GitHub environment `gcp` and set the variables
`tofu output github_actions_variables` prints. Set `GCP_TF_STATE_BUCKET`
to `BUCKET`, without the `gs://` prefix.
