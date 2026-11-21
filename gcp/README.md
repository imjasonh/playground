# GitHub connection for Google Cloud

This stack is the Workload Identity pool and the deploy and plan
accounts that GitHub Actions uses for every app in this project. It is
not an app. Apply it once, before the first app. An app stack does not
create a pool or a GitHub account.

The pool trusts `.github/workflows/deploy-gcp.yml` in one repository,
matched by name and by the numeric IDs of the repository and its owner.
Apply from `main` uses the `github` provider. A pull request plan uses
the `github-plan` provider. `deploy-gcp.yml` selects the GitHub
environment `gcp`, and these accounts accept only that environment. A
plan token cannot apply.

This stack creates each app's runtime service account, listed in
`app_service_accounts`, and the deploy account can act as those accounts
and no others. To add an app, add its account there and apply this
stack before the app's first deploy. The app reads the account with a
`google_service_account` data source. The deploy account cannot create
service accounts, set IAM on one, or change custom roles. It can grant
and revoke only the project roles in `app_project_roles`, so it can't
grant itself Owner or take over another account. The plan account can
read the state bucket and push images. It cannot delete images or read
replica objects.

The stack also sets a monthly budget on the project, $25 by default
(`monthly_budget_usd`). Billing account administrators get an email at
50% and 90% of actual spend and when the month's forecast reaches 100%.
Spend reaches a budget hours after the usage, so treat an alert as a
backstop.

The deploy account can also create and delete budgets on the project's
billing account, and the plan account can view that account's budgets
and costs. The usage-log stack uses this for a $1 monthly budget on its
logs bucket. Re-apply this stack before that budget can be created. The
principal that applies it needs permission to set the billing account's
IAM policy.

This stack also creates a third account, bound to a third provider in
the same pool, so `chrome-extension.yml` can publish the Chrome
extension without a hard-coded refresh token (see
[`chrome-extension/README.md`](../chrome-extension/README.md#publish-from-main)).
That account holds no project roles — a Chrome Web Store access token
isn't a GCP IAM grant — so after `tofu apply` you must link its email
on the publisher in the Chrome Web Store Developer Dashboard (**Account
> API access**) by hand; Terraform cannot do that part.

```bash
gcloud storage buckets create gs://BUCKET --location=us-central1 --uniform-bucket-level-access --public-access-prevention
gcloud storage buckets update gs://BUCKET --versioning

cd terraform
cp terraform.tfvars.example terraform.tfvars   # set project_id, the github_repository values, and state_bucket
tofu init -backend-config="bucket=BUCKET"
tofu apply
```

Use the same bucket the apps use for state. This stack stores its state
under the prefix `github`. App stacks use their own prefix in that bucket.

Create the GitHub environment `gcp` and set the variables
`tofu output github_actions_variables` prints. Set `GCP_TF_STATE_BUCKET`
to `BUCKET`, without the `gs://` prefix.

Create a second GitHub environment, `chrome-webstore`, and set the
variables `tofu output chrome_webstore_github_actions_variables` prints.
Then link `tofu output chrome_webstore_service_account`'s email in the
Chrome Web Store Developer Dashboard. Add the repository secret
`CHROME_WEB_STORE_PUBLISHER_ID` (it does not need to live in the
environment). `chrome-extension.yml` then mints a
`chromewebstore`-scoped access token through this pool instead of a
stored OAuth refresh token.
