# An update on the security of `kontain.me`

On Wednesday November 18th, an attacker compromised the GCP project that runs `kontain.me` and began mining crypto. This is a postmortem of this event.

### How it happened

`kontain.me` is hosted as a number of separate Google Cloud Run services, a Service Account with minimal permissions, a shared Cloud Storage bucket, a load balancer and some GCP-managed DNS entries. The architecture of each of the apps is defined in Terraform in the public https://github.com/imjasonh/kontain.me repo.

To deploy these services automatically, there's a deployer service account, `gha-deployer`, which has permissions to deploy Cloud Run services, manage Service Accounts, buckets, load balancers and DNS entries. That service account can be assumed by a GitHub Actions workflow in the repo, configured using [OIDC Workload Identity Federation](https://docs.github.com/en/actions/how-tos/secure-your-work/security-harden-deployments/oidc-in-google-cloud-platform). All of these trust relationships and the permissions each Service Account is granted is also defined in the public repo.

Workload Identity is a Very Good Thing(tm), but like a lot of good things, it's also complicated. It's easy to get wrong, and I got it wrong, in at least two ways:

1. The rule allowing the GitHub Actions workflow to assume the GCP SA was overly broad. It matched only on the workflow path, `.github/workflows/deploy.yaml`, and did not check that the repo matched `imjasonh/kontain.me`. This was a dumb omission on my part; any GitHub repo that minted an OIDC token from `deploy.yaml` could become my deployer service account.
2. The deployer SA had project-wide `serviceAccount.actAs` permissions. Though the app's service account had minimal permissions (read/write to the one GCS bucket), the project also had the default GCP service account enabled, which had broad **Editor** access to the project.

So, using (1), the attacker was able to run a GHA workflow in their repo and become by deployer. As my deployer, they were able to `actAs` the default GCP SA, which could do ....._anything_. It could enable APIs, create GKE clusters and VMs, request quota increases, and run Vertex AI training jobs. And it did, all of those.

Even if they hadn't acted-as the **Editor** default SA, they could have created and acted-as another SA.

### What the attacker did

The attacker seems to have gained access late Tuesday and made some exploratory requests to make sure they could do what they wanted. On Wednesday around noon Eastern they began creating Vertex AI training runs in three regions. The jobs they ran were actually doing crypto mining, contributing to a wallet they presumably own.

Usage began relatively slowly, at ~$44/hour worth of GPU usage, but within an hour they had requested more GPU quota and began sending more requests to the tune of more than $300/hour. Luckily, I noticed the anomalous traffic and put a stop to it as quickly as I could.

### Where we got lucky

Because kontain.me doesn't normally cost me much money at all, and because I'm constantly paranoid about me doing something stupid (the only smart thing I regularly do!), I had set up a budget alert on the project at $10. The service costs me under $1/month normally, so spending $10 means something is Going Wrong. And that budget alert was 

### Where we are now

I filed a GCP Support ticket for the fraudulent usage, and they were very helpful. At time of writing they're still waiting to tally the total damage. The project is unlinked from billing in the meantime, so kontain.me is down. I may decide not to bring it up again, or if I do I may bring it up in a different shape.

I also reported the GitHub user and repo that ran the fraudulent GHA workflow to get into my GCP project.

The attacker spent between $400-500 of my/Google's money, and I believe gained somewhere around $0.03 worth of crypto. They taught me an important lesson about hosting services on the internet, which I'm sharing with you right now.

### Takeaways

1. Use Workload Identity, but make sure it's tightly constrained. Ask your nearest agent to do a security review and propose fixes.
2. Use only Service Accounts with minimal permissions; disable the GCP default service account. Project-wide `actAs` is full project access otherwise. Avoid project-wide `actAs` while you're at it.
3. Set up budget alerts, and check your email.

I don't know whether my attacker used any kind of AI in their attack; frankly, they probably only needed some GitHub searches and some relatively straightforward bash scripts to probe. I used AI to defend and it made response much faster.
