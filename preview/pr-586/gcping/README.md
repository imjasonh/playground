# gcping

Measure HTTPS latency from your browser to Cloud Storage in each Google
Cloud region. This page is a spiritual successor to
[gcping.com](https://gcping.com), which pinged Cloud Run and is being shut
down.

The page sends GET requests to `storage.REGION.rep.googleapis.com` for a
bucket that does not exist, then keeps updating the median until you stop
it.

The browser reports end-to-end time only. Cloud Storage 404s omit
`Timing-Allow-Origin`, so Resource Timing zeros DNS, TCP, and TLS.

## Run locally

```bash
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```
