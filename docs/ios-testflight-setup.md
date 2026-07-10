# iOS → TestFlight setup: a step-by-step guide

This is the **click-by-click** guide for wiring up the Apple side so that pushing
to `main` builds the iOS app and uploads it to **TestFlight** automatically.
It assumes you have **never done any of this before**. Follow it top to bottom.

By the end you will have added these **GitHub repository secrets**, after which
CI does the rest:

| Secret | Comes from |
|--------|-----------|
| `ASC_KEY_ID` | Step 5 (App Store Connect API key) |
| `ASC_ISSUER_ID` | Step 5 |
| `ASC_API_KEY_P8` | Step 5 (the `.p8` file, base64-encoded) |
| `APPLE_TEAM_ID` | Step 2 (your 10-character Team ID) |
| `MATCH_GIT_URL` | Step 6 (private repo that stores signing files) |
| `MATCH_PASSWORD` | Step 6 (passphrase you choose) |
| `MATCH_GIT_BASIC_AUTHORIZATION` | Step 6 (base64 `user:token` to read that repo) |

> Until all seven exist, CI still runs the tests on every push/PR and simply
> **skips** the TestFlight upload — so nothing breaks while you work through this.

---

## What you need before you start

- **An Apple ID** with **two-factor authentication** turned on. Use one you
  control long-term (ideally a dedicated one for development, not personal).
- **A payment method** — the Apple Developer Program costs **$99 USD/year**.
- **A phone or tablet** to install the TestFlight app on for testing.
- **A computer with Ruby + git** to run one signing command in Step 6. A **Mac
  is easiest**, but this specific command also works on Linux/Windows (WSL). You
  do **not** need a Mac for the day-to-day pipeline — GitHub's macOS runners do
  the building.

**Rough time:** ~30–60 minutes of clicking, plus **waiting for Apple to approve
your enrollment** in Step 1 (often under an hour, occasionally 24–48 hours).

**Jargon cheat-sheet** (don't worry, each is explained when you reach it):

- **Bundle ID** — your app's unique reverse-domain name, e.g.
  `io.github.imjasonh.playground`.
- **Team ID** — a 10-character code identifying your developer account.
- **App Store Connect (ASC)** — Apple's web dashboard for apps & TestFlight.
- **Certificate / Provisioning profile** — the cryptographic files that let a
  build be "signed" as genuinely yours. We let a tool called **fastlane match**
  create and store these so you never touch Keychain by hand.
- **API key (`.p8`)** — a credential that lets our robot (CI) talk to Apple
  without your password.

---

## Step 1 — Enroll in the Apple Developer Program

1. Go to <https://developer.apple.com/programs/enroll/>.
2. Click **Start Your Enrollment** and sign in with your Apple ID.
3. Choose an entity type:
   - **Individual / Sole Proprietor** — simplest; pick this for a personal
     playground. Your legal name shows as the "seller."
   - **Organization** — requires a **D-U-N-S number** and legal authority to
     sign for the company. Only pick this if you have a registered business.
4. Fill in the personal/contact details and agree to the terms.
5. Pay the **$99/year** fee.
6. **Wait for the confirmation email** that says your membership is active. You
   cannot do Steps 3–5 until enrollment is approved.

> If you already have an active membership, skip to Step 2.

---

## Step 2 — Find your Team ID

1. Go to <https://developer.apple.com/account> and sign in.
2. In the sidebar click **Membership details** (older UI: **Membership**).
3. Find **Team ID** — a 10-character string of letters and numbers
   (e.g. `A1B2C3D4E5`).
4. **Copy it.** This becomes the `APPLE_TEAM_ID` secret later.

---

## Step 3 — Register your app's Bundle ID

The **host** app uses `io.github.imjasonh.playground` (see `ios/project.yml`).
In-app experiments share this id — do **not** register a Bundle ID per
experiment.

1. Go to <https://developer.apple.com/account/resources/identifiers/list>
   (**Certificates, Identifiers & Profiles → Identifiers**).
2. Click the blue **+** next to "Identifiers."
3. Select **App IDs** → **Continue**.
4. Select type **App** → **Continue**.
5. Fill in:
   - **Description:** `Playground` (any human-readable label).
   - **Bundle ID:** choose **Explicit** and type
     `io.github.imjasonh.playground` exactly.
6. **Capabilities:** leave unchecked unless you truly need an entitlement
   (most experiments only need Info.plist privacy strings).
7. Click **Continue** → **Register**.

### Step 3b — Keyboard extension Bundle ID (Apple requirement)

A **Custom Keyboard** cannot share the host Bundle ID. Register (or let
**iOS signing bootstrap** create via API):

1. **+** → **App IDs** → **App**.
2. **Description:** `Playground T9 Keyboard`.
3. **Bundle ID:** Explicit → `io.github.imjasonh.playground.t9keyboard`.
4. Capabilities unchecked (sandboxed keyboard).
5. **Register**.

Then run **iOS signing bootstrap** once so match stores
`match AppStore io.github.imjasonh.playground.t9keyboard`. You do **not** repeat
this when adding Ride Monitor–style experiments.

> Skip manual registration if bootstrap’s `ensure_bundle_ids!` creates it for
> you; still run bootstrap so the profile lands in the match repo.

---

## Step 4 — Create the app record in App Store Connect

TestFlight needs an "app" to receive builds into.

1. Go to <https://appstoreconnect.apple.com/apps>.
2. Click the blue **+** → **New App**.
3. Fill in the dialog:
   - **Platforms:** check **iOS**.
   - **Name:** the public app name. ⚠️ This must be **unique across the entire
     App Store**, so `Playground` may be taken — try something like
     `Playground (yourname)`. (You can change it before any public release; it
     doesn't affect TestFlight builds.)
   - **Primary Language:** e.g. English (U.S.).
   - **Bundle ID:** pick `io.github.imjasonh.playground` from the
     dropdown (the one you registered in Step 3).
   - **SKU:** any unique internal string, e.g. `playground` (never shown to users).
   - **User Access:** **Full Access** is fine.
4. Click **Create**.

You now have an app shell. You do **not** need to fill in screenshots,
descriptions, pricing, etc. — those are only for a public App Store release, not
for TestFlight builds distributed to internal testers.

---

## Step 5 — Create an App Store Connect API key

This is the credential CI uses to upload builds. **You can only download the key
file once**, so do this carefully.

1. Go to <https://appstoreconnect.apple.com/access/integrations/api>
   (**Users and Access → Integrations → App Store Connect API**; in older UIs
   this was the **Keys** tab under Users and Access).
2. Make sure the **Team Keys** tab is selected (not "Individual Keys").
3. Click the blue **+** (Generate API Key).
4. Fill in:
   - **Name:** `github-actions-testflight` (any label).
   - **Access / Role:** choose **App Manager**. (Admin also works but grants
     more than needed; App Manager is the least-privilege role that can upload
     to TestFlight.)
5. Click **Generate**.
6. On the keys list you now see three things you need:
   - **Issuer ID** — shown near the top of the page, a long UUID like
     `69a6de70-...`. → becomes `ASC_ISSUER_ID`.
   - **Key ID** — the 10-character ID in the row for your new key. → becomes
     `ASC_KEY_ID`.
   - **Download** — click **Download API Key** in the row's menu to get a file
     named `AuthKey_XXXXXXXXXX.p8`. Save it somewhere safe. **This download is
     one-time-only.** → becomes `ASC_API_KEY_P8` (base64-encoded, see Step 7).

> Treat the `.p8` like a password. If you lose it or it leaks, **revoke** the key
> here and generate a new one.

---

## Step 6 — Set up code signing with fastlane match

"Signing" proves a build is genuinely from you. Doing it by hand (certificates,
private keys, provisioning profiles, Keychain) is the most error-prone part of
iOS. We avoid all of that with **fastlane match**, which:

- creates a **distribution certificate** and an **App Store provisioning
  profile** for your bundle ID, and
- stores them, **encrypted**, in a **separate private git repo**, so CI can fetch
  them read-only.

### 6a. Create the private "signing" repo

1. On GitHub, create a **new, empty, PRIVATE** repository — for example
   `imjasonh/ios-signing`. **Do not** add a README (empty is fine).
   ⚠️ It **must be private** — it will hold your signing certificate.
2. Copy its HTTPS URL, e.g. `https://github.com/imjasonh/ios-signing.git`.
   → this becomes `MATCH_GIT_URL`.

### 6b. Make a token so match (and CI) can read that repo

1. Go to <https://github.com/settings/personal-access-tokens> → **Fine-grained
   tokens** → **Generate new token**.
2. Set:
   - **Token name:** `ios-signing-read`.
   - **Expiration:** your choice (e.g. 1 year — set a reminder to rotate).
   - **Repository access:** **Only select repositories** → pick your
     `ios-signing` repo.
   - **Permissions → Repository permissions → Contents:** **Read and write**
     (match needs write the first time to store certs; CI only reads).
3. **Generate** and copy the token (starts with `github_pat_...`). Keep it handy
   for the next steps.

### 6c. Choose your passphrase now

Pick a strong passphrase for match and keep it safe — it encrypts the signing
files in the repo. This value becomes your **`MATCH_PASSWORD`** secret.

You do **not** run any command yet. The certificate itself is created in **Step
9**, *after* the secrets are in place — either automatically in CI (recommended,
no Mac needed) or locally. Continue to Step 7.

> **Never run `fastlane match nuke`** unless you intend to revoke and recreate
> all certificates — it deletes them from Apple.

---

## Step 7 — Turn the files/values into secret-ready strings

Two secrets need encoding. Run these on your computer:

**The API key (`.p8`) → `ASC_API_KEY_P8`:**

```bash
# macOS:
base64 -i AuthKey_XXXXXXXXXX.p8 | pbcopy      # now in your clipboard
# Linux:
base64 -w0 AuthKey_XXXXXXXXXX.p8              # copy the printed line
```

We store it base64-encoded so newlines in the key survive being pasted into a
GitHub secret. (The pipeline decodes it automatically — the Fastfile passes
`is_key_content_base64: true`.)

**The repo token → `MATCH_GIT_BASIC_AUTHORIZATION`** (same value you exported in
Step 6c):

```bash
printf 'YOUR_GH_USERNAME:github_pat_XXXX' | base64      # Linux
printf 'YOUR_GH_USERNAME:github_pat_XXXX' | base64 | pbcopy   # macOS
```

---

## Step 8 — Add the secrets to this repository

1. In **this** repo (the playground) go to **Settings → Secrets and variables →
   Actions**.
2. Click **New repository secret** and add each of the following (name on the
   left must match **exactly**):

| Secret name | Value to paste |
|-------------|----------------|
| `ASC_KEY_ID` | The 10-char Key ID from Step 5 |
| `ASC_ISSUER_ID` | The Issuer UUID from Step 5 |
| `ASC_API_KEY_P8` | The **base64** blob from Step 7 |
| `APPLE_TEAM_ID` | Your 10-char Team ID from Step 2 |
| `MATCH_GIT_URL` | `https://github.com/imjasonh/ios-signing.git` |
| `MATCH_PASSWORD` | The passphrase you chose in Step 6c |
| `MATCH_GIT_BASIC_AUTHORIZATION` | The **base64** `user:token` from Step 7 |

3. Double-check spelling of every secret **name** — a typo means CI silently
   can't find it and the upload fails.

---

## Step 9 — Create your signing certificate (one time)

Now that the secrets exist, create the distribution certificate + App Store
provisioning profile and store them (encrypted) in your `ios-signing` repo. Do
this **once**. Pick one option:

### Option A (recommended — no Mac needed): run it in CI

1. In this repo go to the **Actions** tab → **iOS signing bootstrap** workflow.
2. Click **Run workflow**, leave the app as `ios`, and **Run**.
3. It runs on a macOS runner, creates the certificate + profile via your API
   key, encrypts them with `MATCH_PASSWORD`, and pushes them to `ios-signing`.
   When it's green, signing is ready.

If it fails complaining a secret is missing, finish Step 8 and re-run it.

### Option B: run it locally (needs Ruby; Mac or Linux/WSL)

```bash
cd ios
gem install fastlane          # skip if already installed

export MATCH_GIT_URL="https://github.com/imjasonh/ios-signing.git"
export MATCH_PASSWORD="the-passphrase-you-chose"
export MATCH_GIT_BASIC_AUTHORIZATION="$(printf 'YOUR_GH_USERNAME:github_pat_XXXX' | base64)"
export ASC_KEY_ID="XXXXXXXXXX"
export ASC_ISSUER_ID="xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx"
export ASC_API_KEY_P8="$(base64 < /path/to/AuthKey_XXXXXXXXXX.p8)"
export APPLE_TEAM_ID="A1B2C3D4E5"

bundle install
bundle exec fastlane signing_bootstrap
```

Either way, match creates a **distribution certificate** and **App Store
provisioning profiles** named like
`match AppStore io.github.imjasonh.playground` and
`match AppStore io.github.imjasonh.playground.t9keyboard`
(one profile per App ID in `ios/fastlane/Matchfile`) and stores them in the
`ios-signing` repo. Future TestFlight builds read them read-only. Re-run
bootstrap when the certificate expires or you add another **app extension**
Bundle ID — not when you add in-app experiments.

---

## Step 10 — Add yourself as a TestFlight tester

So you actually receive the build.

1. Install the **TestFlight** app from the App Store on your iPhone/iPad.
2. In App Store Connect open your app → **TestFlight** tab → **Internal
   Testing**.
3. Click **+** next to "Internal Testing" to create a group, name it e.g.
   `Devs`.
4. Add testers: they must be users in **Users and Access** (add yourself/others
   there first if needed). **Internal** testers get every new build immediately,
   **with no Beta App Review**.
5. After the first build finishes processing (Step 11), you'll get a TestFlight
   invite; accept it in the TestFlight app to install.

> **External testers** (people outside your ASC team, up to 10,000) are also
> possible but require a one-time **Beta App Review** per version and a bit more
> metadata (beta description, contact email). Start with internal testing; ask me
> and I can extend the pipeline to push to an external group.

---

## Step 11 — Ship it and verify

1. **Merge this PR to `main`** (the iOS workflow must be on `main` for
   push-to-main delivery), or push any change under `ios/` to `main`.
2. Go to the repo's **Actions** tab → the **iOS** workflow run.
   - The `discover` job detects the changed iOS app.
   - The `ios` job (on macOS) generates the project, runs tests, and — because
     it's a push to `main` **with** the secrets present — runs `fastlane beta`.
3. In **App Store Connect → your app → TestFlight**, the new build appears with
   status **Processing** for a few minutes, then becomes available to your
   internal group.
4. Open **TestFlight** on your device → install → 🎉.

---

## Troubleshooting

- **"TestFlight upload skipped" warning in CI, tests pass:** the secrets aren't
  all set yet (the deploy gate checks `ASC_KEY_ID`). Recheck Step 8.
- **`No matching provisioning profiles found` / signing errors:** the host app
  profile name must be `match AppStore io.github.imjasonh.playground` (and the
  keyboard extension
  `match AppStore io.github.imjasonh.playground.t9keyboard`). Re-run the
  **iOS signing bootstrap** workflow (Step 9) if you added an extension and the
  match repo does not yet contain its profile, and confirm `APPLE_TEAM_ID` is
  correct.
- **`Authentication credentials are missing or invalid` from Apple:** the API
  key is wrong or lacks permission. Confirm `ASC_KEY_ID` / `ASC_ISSUER_ID`, that
  `ASC_API_KEY_P8` is the **base64** of the `.p8`, and that the key's role is
  **App Manager**.
- **match can't read the signing repo:** `MATCH_GIT_URL` must be the HTTPS URL,
  and `MATCH_GIT_BASIC_AUTHORIZATION` must be base64 of `username:token` for a
  token with **Contents** access to that private repo.
- **`Redundant Binary Upload` / build number already exists:** each upload needs
  a unique build number. The Fastfile bumps it from the latest TestFlight build
  automatically; if the API lookup fails it falls back to the CI run number —
  just re-run the job.
- **Build stuck "Processing" a long time:** normal for the first build; Apple can
  take 10–30 minutes. It'll clear.
- **Export compliance prompt:** already handled — `project.yml` sets
  `ITSAppUsesNonExemptEncryption = NO`. If your real app *does* use custom
  encryption, that answer must change.

## Security notes

- The `ios-signing` repo and every secret above are sensitive. Keep the signing
  repo **private**; never commit `.p8`, `.p12`, `.mobileprovision`, or
  certificates into **this** repo (`.gitignore` already blocks them).
- Rotate the API key and the fine-grained token periodically; revoke immediately
  if either leaks.
- GitHub masks secret values in logs, but avoid `echo`-ing them in workflow steps
  anyway.

---

Once all seven secrets are in place, this is fully hands-off: every push to
`main` that touches an iOS app ships a fresh TestFlight build. See
[`ios-testflight-design.md`](ios-testflight-design.md) for the overall design and
the (not-yet-implemented) PR-preview options.
