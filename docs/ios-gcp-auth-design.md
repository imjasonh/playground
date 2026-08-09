# Design: authenticating the iOS app to Google Cloud

> Implemented as the **GCP Auth** experiment in
> [`ios/Sources/Experiments/GCPAuth/`](../ios/Sources/Experiments/GCPAuth). It
> ships **unconfigured**: with no Firebase project wired up it answers its own
> network calls in-process, so it runs in the Simulator and in CI without
> credentials. Point it at a project (below) to exercise the live chain.

## The constraint everything follows from

**An iOS app cannot keep a secret.** Anything in the binary, the `Info.plist`,
or an embedded plist is extractable by anyone who downloads the IPA and runs
`strings` on it. A GCP service account JSON key in an app is therefore the worst
available option — Google effectively deprecated the pattern and ships an org
policy, `constraints/iam.disableServiceAccountKeyCreation`, to ban it outright.

So the app ships no credential. The only private key involved is generated
*on the device* inside the Secure Enclave, is not extractable even by the app
that created it, and never leaves. Everything else is a short-lived token.

## Two questions, often conflated

|  | Question | Mechanism | Strength |
|--|----------|-----------|----------|
| **Identity** | Who is the user? | Sign in with Apple / OIDC, or anonymous Firebase auth | Real cryptographic authentication |
| **Integrity** | Is this a genuine copy of my app? | Apple **App Attest**, surfaced as Firebase **App Check** | Hardware-backed *risk signal*, not authorization |

Most "how does my app authenticate to GCP" questions are really the second one,
and the honest answer is that attestation raises the cost of impersonation a
great deal without reducing it to zero. Apple says as much: treat App Attest as
a signal, never as the only gate.

## The chain

```
  ┌─────────────────────────── iPhone ───────────────────────────┐
  │                                                              │
  │  Secure Enclave key ──generateKey / attestKey──▶ attestation │
  │                                                              │
  └────────────────────────────┬─────────────────────────────────┘
                               │  1
                               ▼
              Firebase App Check  ──▶  App Check token (JWT signed by Google)
                               │
                               │  2  X-Firebase-AppCheck: <token>
                               ▼
              Firebase Auth  ──▶  Firebase ID token
                                  iss = securetoken.google.com/<project-id>
                               │
                               │  3  RFC 8693 token exchange
                               ▼
              Google STS  ──▶  short-lived access token
                               │
                               │  3b (optional)
                               ▼
              IAM Credentials  ──▶  impersonated service account token
```

### 1. App Attest → App Check

`DCAppAttestService.generateKey()` creates a P-256 keypair in the Secure
Enclave. `attestKey(_:clientDataHash:)` returns a CBOR attestation object with
an X.509 chain rooted in Apple's App Attest Root CA. A verifier checks that
chain, that the one-time challenge it issued is embedded in the leaf
certificate's custom extension (OID `1.2.840.113635.100.8.2`), and that the
authenticator data's RP ID hash equals `SHA256("<TeamID>.<BundleID>")`.

Firebase App Check does that verification for you over three REST calls, so the
app needs no Firebase SDK:

| Call | Purpose |
|------|---------|
| `…/apps/{appId}:generateAppAttestChallenge` | one-time nonce |
| `…/apps/{appId}:exchangeAppAttestAttestation` | attestation → `artifact` + App Check token |
| `…/apps/{appId}:exchangeAppAttestAssertion` | cheap re-issue from then on |

What gets signed matters and is easy to get wrong:

- **Attestation** signs `SHA256(challenge)`. The challenge is what stops a
  captured attestation being replayed.
- **Assertion** signs `SHA256(artifact ‖ challenge)`. The artifact ties the
  assertion back to the key that was already attested; the fresh challenge makes
  each one single-use. This mirrors what the Firebase App Check SDK signs, and
  it is what the service recomputes.

Both are in
[`GCPAuthAttestor.swift`](../ios/Sources/Experiments/GCPAuth/GCPAuthAttestor.swift)
as `GCPAuthClientData`.

The App Check token that comes back is a JWT signed by Google. Any backend can
verify it against `https://firebaseappcheck.googleapis.com/v1/jwks`, expecting
issuer `https://firebaseappcheck.googleapis.com/<project-number>` and audience
`projects/<project-number>` — no call to Apple required.

### 2. App Check → Firebase Auth

Every Firebase Auth request carries `X-Firebase-AppCheck: <token>`. That header
is what lets you switch on App Check **enforcement** for Identity Platform:
sign-in attempts that didn't come from an attested install are refused before
they ever mint an ID token.

The experiment defaults to **anonymous** sign-in (`accounts:signUp`). It still
produces a real per-install Firebase user with a stable `sub`, which is all the
federation step needs, and unlike Sign in with Apple it requires no entitlement.
The Apple path (`accounts:signInWithIdp` with `providerId=apple.com`) is
implemented alongside it — see "Sign in with Apple" below.

The nonce handling is worth spelling out: Apple gets the **hashed** nonce in
`ASAuthorizationAppleIDRequest.nonce`, and Firebase gets the **raw** one in the
`postBody`. Firebase hashes what you send and compares, which is what proves
this app requested that particular token rather than replaying someone else's.

### 3. Firebase ID token → Google STS

Workload Identity Federation trades an OIDC token for a Google one. The pool
provider is created with Firebase's issuer, so STS verifies the ID token's
signature against `securetoken.google.com`'s JWKS and maps its claims onto a
Google principal. The exchange is form-encoded RFC 8693 against
`https://sts.googleapis.com/v1/token`, and the reply is an access token good for
about an hour. Nothing long-lived crosses the wire in either direction.

Optionally the federated principal then impersonates a service account via
`iamcredentials.googleapis.com/…:generateAccessToken`. Only worth doing when the
app needs permissions you'd rather not grant to the whole pool, and it should be
a purpose-built account with the narrowest role that works: impersonation hands
the client everything that account can do, for the life of the token.

## The caveat that decides the architecture

**Google's STS does not look at App Check.** It validates the Firebase ID token
and nothing else. Attestation is enforced by Firebase Auth and by whatever
backend you write — it is not in the enforcement path of the token exchange. A
client holding a valid Firebase ID token can federate with it however that token
was obtained.

That is the concrete reason the stronger design keeps the app out of GCP IAM
entirely:

- The app calls **your** service (Cloud Run, API Gateway) with a user ID token
  plus an App Check token.
- Your service verifies both, decides, and does the privileged work under its
  own attached service identity — no key file anywhere.
- The blast radius of a compromised client is one user's permissions instead of
  a service account's.

Where the client genuinely must talk to Google directly — large media uploads
you don't want to proxy — hand out something narrow rather than a general
credential: a **V4 signed URL** scoped to one object for a few minutes, or a
**downscoped token** where your backend exchanges its own access token at STS
with a Credential Access Boundary restricting it to a bucket prefix.

The experiment federates straight from the client because that is the thing
worth showing end to end on a phone. The UI says so on screen.

## Wiring it to a real project

Nothing in the configuration is secret — the Firebase Web API key identifies
*which project* you're talking to, not *who you are*.

### Firebase side

1. Register the iOS app in the Firebase console and note the App ID
   (`1:<project-number>:ios:<hash>`).
2. App Check → register the app with the **App Attest** provider.
3. Turn on App Check enforcement for Identity Platform once real traffic looks
   healthy in the metrics, not before.

### GCP side

```bash
PROJECT_ID=my-project
PROJECT_NUMBER=123456789012

gcloud iam workload-identity-pools create playground-ios-pool \
  --location=global --display-name="Playground iOS"

gcloud iam workload-identity-pools providers create-oidc firebase-auth \
  --location=global \
  --workload-identity-pool=playground-ios-pool \
  --issuer-uri="https://securetoken.google.com/${PROJECT_ID}" \
  --allowed-audiences="${PROJECT_ID}" \
  --attribute-mapping="google.subject=assertion.sub,attribute.provider=assertion.firebase.sign_in_provider"
```

Grant the pool's principals something — ideally scoped to one subject rather
than the whole pool:

```bash
gcloud storage buckets add-iam-policy-binding gs://my-bucket \
  --role=roles/storage.objectViewer \
  --member="principalSet://iam.googleapis.com/projects/${PROJECT_NUMBER}/locations/global/workloadIdentityPools/playground-ios-pool/*"
```

For the optional impersonation hop:

```bash
gcloud iam service-accounts add-iam-policy-binding \
  ios-app@${PROJECT_ID}.iam.gserviceaccount.com \
  --role=roles/iam.workloadIdentityUser \
  --member="principalSet://iam.googleapis.com/projects/${PROJECT_NUMBER}/locations/global/workloadIdentityPools/playground-ios-pool/*"
```

In production you would also want an attribute condition excluding anonymous
users:

```
--attribute-condition="assertion.firebase.sign_in_provider != 'anonymous'"
```

which is precisely why this experiment's default (anonymous auth, for the sake
of running without a signing bootstrap) is a demo posture and not a production
one.

### App side

Add a `GCPAuth` dictionary to the Playground `Info.plist` (via `info.properties`
in `ios/project.yml`). Absent that key, `GCPAuthConfiguration.fromBundle()`
returns the unconfigured placeholder and the experiment runs simulated.

| Key | Example |
|-----|---------|
| `ProjectID` | `my-project` |
| `ProjectNumber` | `123456789012` |
| `APIKey` | `AIza…` (Firebase Web API key) |
| `AppID` | `1:123456789012:ios:abc123` |
| `WorkloadIdentityPoolID` | `playground-ios-pool` |
| `WorkloadIdentityProviderID` | `firebase-auth` |
| `ServiceAccountEmail` | optional; empty means "stay the federated principal" |
| `AppleSignInEnabled` | optional bool, default false |

Info.plist keys are not App ID capabilities, so adding them does **not** require
a signing bootstrap.

## Sign in with Apple

Implemented in
[`GCPAuthAppleSignIn.swift`](../ios/Sources/Experiments/GCPAuth/GCPAuthAppleSignIn.swift)
but **off by default**. Turning it on needs the
`com.apple.developer.applesignin` entitlement plus the matching App ID
capability, and per [`ios/AGENTS.md`](../ios/AGENTS.md) that means a one-time
signing re-bootstrap. `fastlane signing_bootstrap` currently enables only
HealthKit, so enabling Apple sign-in would also mean teaching `ensure_*!` about
the new capability before `fastlane beta` could archive a build that carries it.
Anonymous auth demonstrates the same chain and costs none of that.

## Simulated mode

With no project configured the experiment swaps in two stand-ins:

- `GCPAuthSimulatedAttestor` in place of `DCAppAttestService`, which does not
  exist in the Simulator.
- `GCPAuthSimulatedTransport` in place of `URLSession`, answering every endpoint
  in-process.

The tokens it mints are structurally real JWTs with the right issuers,
audiences, and claim shapes — and a signature segment that is a literal string.
Anything that actually verified them would reject them, which is the point:
there is no way to mistake the simulated path for authentication. It exists so
the experiment runs on a Simulator with no network, and so the UI test in CI has
something deterministic to drive.

## Testing

`ios/Tests/PlaygroundTests/GCPAuthTests.swift` covers the pure pieces (duration
and timestamp parsing, base64 alphabets, form encoding, JWT claim extraction,
token expiry skew, Google's error envelope) and drives the whole chain over a
recording transport, asserting:

- the first run attests a key and stores the artifact;
- the second run *asserts* the stored key instead of attesting again;
- a 4xx on assertion re-attests once, rather than stranding the install;
- a 5xx does **not**, so a backend blip doesn't burn App Attest's key-creation
  rate limit;
- sign-in carries `X-Firebase-AppCheck`;
- federation sends a correctly form-encoded RFC 8693 exchange;
- impersonation only happens when a service account is configured.

## References

- Apple, [Establishing your app's integrity](https://developer.apple.com/documentation/devicecheck/establishing-your-app-s-integrity)
- Apple, [Validating apps that connect to your server](https://developer.apple.com/documentation/devicecheck/validating-apps-that-connect-to-your-server)
- Firebase, [App Check with App Attest on Apple platforms](https://firebase.google.com/docs/app-check/ios/app-attest-provider)
- Google Cloud, [Workload Identity Federation](https://cloud.google.com/iam/docs/workload-identity-federation)
- RFC 8693, OAuth 2.0 Token Exchange
