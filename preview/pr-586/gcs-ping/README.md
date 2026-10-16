# GCS ping

Measure HTTPS latency from your browser to Cloud Storage in each Google
Cloud region. The page sends GET requests to
`storage.REGION.rep.googleapis.com` for a bucket that does not exist, then
shows the median time until the 404 comes back. The layout follows
[GCPing](https://github.com/GoogleCloudPlatform/gcping).

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
