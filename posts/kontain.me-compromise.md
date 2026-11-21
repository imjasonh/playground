# An update on the security of `kontain.me`

On Wednesday, November 18th, 2026, an attacker compromised the GCP project that runs [kontain.me](https://github.com/imjasonh/kontain.me) and began mining crypto. This is a postmortem of the incident.

No users of kontain.me (if any) were harmed; no malicious data was served to users, no contents were taken.

## How it happened

`kontain.me` runs on a number of separate Google Cloud Run services, a Service Account with minimal permissions, a shared Cloud Storage bucket, a load balancer and some GCP-managed DNS entries. The architecture of each of the apps is defined in Terraform in the public https://github.com/imjasonh/kontain.me repo.

To deploy these services automatically, there's a deployer service account, `gha-deployer`, which has permissions to deploy Cloud Run services, manage Service Accounts, buckets, load balancers and DNS entries. That service account can be assumed by a GitHub Actions workflow in the repo, configured using [OIDC Workload Identity Federation](https://docs.github.com/en/actions/how-tos/secure-your-work/security-harden-deployments/oidc-in-google-cloud-platform). The trust relationships were not defined in Terraform, but were instead click-opsed at some point in the forgotten past.

Workload Identity is a Very Good Thing(tm), but like a lot of good things, it's also complicated. It's easy to get wrong, and I got it wrong, in at least two ways:

1. The rule allowing the GitHub Actions workflow to assume the GCP SA was overly broad. It matched only on the workflow path, `.github/workflows/deploy.yaml`, and did not check that the repo matched `imjasonh/kontain.me`. This was a dumb omission on my part; any GitHub repo that minted an OIDC token from `deploy.yaml` could become my deployer service account.
2. The deployer SA had project-wide `iam.serviceAccounts.actAs` permissions. Though the app's service account had minimal permissions (read/write to the one GCS bucket), the project also had the default GCP service account enabled, which had broad **Editor** access to the project. This is the classic `<project-number>@compute.gserviceaccount.com` account.

So, using (1), the attacker was able to run a GHA workflow in their repo and become my deployer. As my deployer, they were able to `actAs` the default GCP SA, which could do ....._anything_. It could enable APIs, create GKE clusters and VMs, request quota increases, and run Vertex AI training jobs. And it did, all of those.

Even if they hadn't acted-as the **Editor** default SA, they could have created and acted-as another SA.

Upon noticing the fraudulent usage, I immediately disabled the SA being used to create new jobs, and unlinked billing. However, this didn't stop the resources in use, and GCP prevented me from canceling or deleting Vertex AI jobs while billing was unlinked🤦. I re-linked billing, cancelled jobs, and re-un-linked. Because jobs were spread across many regions, and because the GCP UI doesn't let me bulk-delete jobs, I had my agent write a script that would cancel all jobs one-by-one.

## What the attacker did

The attacker seems to have gained access late Tuesday and made some exploratory requests to make sure they could do what they wanted. On Wednesday around noon Eastern they began creating Vertex AI training runs in three regions. The jobs they ran were actually doing crypto mining, contributing to a wallet they presumably own.

Spend began relatively slowly, at ~$44/hour worth of GPU usage, but within an hour they had requested more GPU quota and began sending more requests to the tune of more than $300/hour. Luckily, I noticed the anomalous traffic and put a stop to it as quickly as I could.

## Where we got lucky

Because kontain.me doesn't normally cost me much money at all, and because I'm constantly paranoid about me doing something stupid (the only smart thing I regularly do!), I had set up a budget alert on the project at $10. The service costs me under $1/month normally, so spending $10 means something is Going Wrong. That budget alert was tripped quickly after the attack began in earnest, and by the time I saw it they'd already hit >$40 of usage.

## Where we are now

I filed a GCP Support ticket for the fraudulent usage, and they were very helpful. At the time of writing they're still tallying the total damage; they say it can take a few days after the last fraudulent usage to assess the total bill. The project is unlinked from billing in the meantime, so kontain.me is down. I may decide not to bring it up again, or if I do I may bring it up in a different shape.

I also reported the GitHub user and repo that ran the fraudulent GHA workflow to get into my GCP project.

The attacker spent $400-$500 of my/Google's money, and I believe gained somewhere around $0.03 worth of crypto. They taught me an important lesson about hosting services on the internet, which I'm sharing with you right now.

## Takeaways

1. Use Workload Identity, but make sure it's tightly constrained. Ask your nearest agent to do a security review and propose fixes.
2. Use only Service Accounts with minimal permissions; disable the GCP default service account. Project-wide `actAs` is full project access otherwise. Avoid project-wide `actAs` while you're at it.
3. Set up budget alerts, and check your email.

I don't know whether my attacker used any kind of AI in their attack; frankly, they probably only needed some GitHub searches and some relatively straightforward bash scripts to probe. I used AI to defend and it made responding much faster, by parsing thousands of audit log entries, and immediately identifying the behavior. Response would have taken much longer without it, and with this attack, time was literally money.

Ultimately, this was my boneheaded mistake, and GCP has been very helpful in getting it resolved.
