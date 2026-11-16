# stream-boids

A Go program that renders a flock of boids and streams it, with a generated
soundtrack, to YouTube Live through ffmpeg. Each viewer adds a boid, up to
10,000. A member who chats gets a gold boid with their name on it. Super
Chats, Super Stickers, and memberships push the flock apart, ring a bell, and
show a thank-you banner. A HUD in the corner shows the viewer count and how
many members are watching.

It runs as a container on one Spot VM in Compute Engine. When Compute Engine
preempts the VM, the VM stops, the managed instance group starts it again
when its zone has capacity, and the program reconnects to the same YouTube
stream key.

## How it works

The program draws each frame on the CPU, in parallel across every core, and
writes raw RGBA video and PCM audio to ffmpeg's standard input. ffmpeg
encodes H.264 and AAC and sends FLV over RTMPS to YouTube's ingest server.

- **Reconnect.** When ffmpeg exits, the encoder starts a new one after a
  backoff of 1 to 30 seconds and asks Secret Manager for the stream key
  again. While ffmpeg is down, the program keeps the simulation running but
  skips rendering. On YouTube, a scheduled stream with **Auto-start** on and
  **Auto-stop** off stays on the same broadcast while the encoder is away,
  so a preempted VM resumes the same video and chat.
- **Viewers.** The program reads the broadcast's concurrent viewer count
  every 60 seconds and moves the boid count toward it. It never draws fewer
  than `MIN_BOIDS` or more than `BOID_CAP`. When the channel hides the count,
  the HUD shows `-- viewers` and the flock follows the members alone.
- **Members.** YouTube doesn't say which members are watching, so the
  program counts a member as watching for 30 minutes after their last chat
  message or membership event.
- **Super Chats.** The program reads chat every 75 seconds, or less often
  when YouTube asks it to. Higher tiers push harder, ring a higher bell, and
  keep their banner up longer. Events from before the program started are
  not replayed.

## Run locally

You need Go and ffmpeg. You don't need YouTube credentials:
`cmd/fake-youtube` serves the parts of the YouTube Data API that the program
calls, with a page where you set the viewer count and send chat messages,
Super Chats, and memberships.

1. Start the fake API:

   ```bash
   go run ./cmd/fake-youtube
   ```

   Open `http://127.0.0.1:8090/` to control it.

1. In another terminal, stream to a file:

   ```bash
   OUTPUT_URL=out.flv \
   YOUTUBE_API_BASE=http://127.0.0.1:8090/youtube/v3 \
   VIDEO_ID=fakeVideo01 \
   go run .
   ```

   Or watch it live. In a third terminal, start a player that listens for
   RTMP. Its window opens when the first frames arrive:

   ```bash
   ffplay -f flv -listen 1 -i rtmp://127.0.0.1:1935/live/test
   ```

   Then point `OUTPUT_URL` at it:

   ```bash
   OUTPUT_URL=rtmp://127.0.0.1:1935/live/test \
   YOUTUBE_API_BASE=http://127.0.0.1:8090/youtube/v3 \
   VIDEO_ID=fakeVideo01 \
   go run .
   ```

   To skip the fake API, leave out `YOUTUBE_API_BASE` and `VIDEO_ID` and set
   `STATIC_VIEWERS=500`.

For a smaller, cheaper stream on a laptop, add `WIDTH=1280 HEIGHT=720 FPS=30`.

### Stream to YouTube from your computer

Secret Manager needs a GCE VM, so locally the keys come from files. Save the
stream key from YouTube Studio (**Go live** > **Stream**) to a file outside
the repository:

```bash
mkdir -p ~/.config/stream-boids
read -rs KEY && printf '%s' "$KEY" > ~/.config/stream-boids/stream-key && unset KEY
chmod 600 ~/.config/stream-boids/stream-key
```

Then stream with a fixed viewer count, which needs no API key:

```bash
STREAM_KEY_FILE=~/.config/stream-boids/stream-key \
STATIC_VIEWERS=200 \
WIDTH=1280 HEIGHT=720 FPS=30 VIDEO_BITRATE=4000000 \
go run .
```

To follow real viewers and chat, save a YouTube Data API key the same way
and replace `STATIC_VIEWERS` with
`YOUTUBE_API_KEY_FILE=~/.config/stream-boids/api-key` and either
`CHANNEL_ID` or `VIDEO_ID`. The default 12 Mbps at 1080p60 needs that much
upload bandwidth.

Run the tests:

```bash
go test -race ./...
```

`TestStreamsToFile` runs the whole program against the fake API and real
ffmpeg for 3 seconds, then checks the output with ffprobe. It skips when
either command is missing.

## Configuration

The program reads its configuration from environment variables.

| Variable | Default | Meaning |
|---|---|---|
| `WIDTH`, `HEIGHT` | `1920`, `1080` | Frame size. Both must be even. |
| `FPS` | `60` | Frames per second. Must divide 48000. |
| `BOID_CAP` | `10000` | The most boids. |
| `MIN_BOIDS` | `1` | The fewest boids. |
| `WORKERS` | `GOMAXPROCS` | Goroutines that simulate and render. |
| `STATIC_VIEWERS` | `0` | The viewer count when no video or channel is set. |
| `OUTPUT_URL` | none | Stream here instead of YouTube: a file or an RTMP URL. |
| `OUTPUT_FORMAT` | `flv` | ffmpeg's output format. |
| `INGEST_URL` | `rtmps://a.rtmps.youtube.com:443/live2` | YouTube's ingest server. The stream key is appended. |
| `FFMPEG` | `ffmpeg` | The ffmpeg command. |
| `VIDEO_BITRATE` | `12000000` | Video bits per second. |
| `X264_PRESET` | `veryfast` | x264 preset. |
| `STREAM_KEY_SECRET` | none | Secret Manager secret that holds the stream key. |
| `STREAM_KEY_FILE` | none | File that holds the stream key. |
| `YOUTUBE_API_KEY_SECRET` | none | Secret Manager secret that holds a YouTube Data API key. |
| `YOUTUBE_API_KEY_FILE` | none | File that holds a YouTube Data API key. |
| `YOUTUBE_API_BASE` | `https://www.googleapis.com/youtube/v3` | The API endpoint. |
| `VIDEO_ID` | none | The broadcast to watch. |
| `CHANNEL_ID` | none | The channel to search for a live broadcast when `VIDEO_ID` is empty. |
| `VIEWER_POLL` | `60s` | How often to read the viewer count. |
| `CHAT_POLL` | `75s` | The shortest wait between chat reads. |
| `SEARCH_INTERVAL` | `30m` | How often to search the channel while no broadcast is live. |
| `MEMBER_WINDOW` | `30m` | How long a member counts as watching after they chat. |
| `QUOTA_PAUSE` | `1h` | How long to stop calling the API after a quota error. |
| `METRICS_INTERVAL` | `60s` | How often to log frame time, drops, and ffmpeg restarts. |
| `LOG_LEVEL` | `info` | Log level. |

A secret is a Secret Manager secret ID in the VM's project, or a full
resource name that starts with `projects/`. Set the secret or the file for
each key, not both.

## Secrets

The stream key and the API key never appear in Terraform, its state, a plan
comment, an environment variable, the instance metadata, or a log line:

- Terraform creates the two Secret Manager secrets with no versions. You add
  the values with `gcloud`, which reads them from standard input.
- The VM's service account can read those two secrets and nothing else in
  Secret Manager. The program fetches them over REST with a token from the
  metadata server, so the VM has no key file.
- The program reads the stream key again before each ffmpeg start, so a new
  key takes effect on the next reconnect. It passes the ingest URL to ffmpeg
  as an argument and never logs it, and it removes the URL from ffmpeg's
  error output before logging that.
- The deploy account that `deploy-gcp.yml` uses can create secrets and set
  who reads them, but it holds no role that reads or adds a value. The plan
  account can only list them.
- The VM has no firewall rules that allow inbound traffic, OS Login is on,
  and project-wide SSH keys are blocked.

## Deploy

`deploy-gcp.yml` applies `terraform/` from `main` and comments a plan on pull
requests, as it does for `cloudrun-sqlite`. The stack creates:

- An Artifact Registry repository. Terraform builds the base image with
  [apko](https://github.com/chainguard-dev/apko) from `apko.yaml`: Chainguard
  packages from `apk.cgr.dev/chainguard`, including ffmpeg 9.0. Then it
  builds the program onto that base with [ko](https://ko.build). Both images
  are built for linux/amd64 and linux/arm64.
- A Spot VM template that runs Container-Optimized OS, and a regional managed
  instance group of one VM. The default machine, `n4a-highcpu-2`, streams
  1280x720 at 30 fps; see [Performance and cost](#performance-and-cost). Each VM gets an ephemeral external IP and no
  inbound firewall rules. cloud-init starts the container under systemd.
- The VM's service account, the two secrets, and a VPC.

### One-time setup

1. Apply `gcp/terraform` again, so the deploy and plan accounts get the
   Compute Engine and Secret Manager roles this stack needs.

1. On YouTube Studio, schedule a stream:
   - Choose a persistent stream key, not one that YouTube creates for this
     stream.
   - Turn **Auto-start** on and **Auto-stop** off.
   - Turn on live chat.

1. In the [Google Cloud console](https://console.cloud.google.com/apis/credentials),
   create an API key that can call only the YouTube Data API v3. Terraform
   enables that API in the project.

1. Set `video_id` to the scheduled stream's video ID, or `channel_id` to the
   channel, in `terraform/variables.tf`. `deploy-gcp.yml` passes only
   `project_id`, so other settings are variable defaults. A video ID costs
   less quota; see [Quota](#quota).

1. Merge to `main`, then add the secret values. The `add_secrets` output
   prints these commands:

   ```bash
   gcloud secrets versions add stream-key --project=PROJECT --data-file=-
   gcloud secrets versions add youtube-api-key --project=PROJECT --data-file=-
   ```

   Type or paste the value, then press Control+D. Until the stream key
   exists, the program logs that it can't read it and retries.

The VM is disabled by default: `running` defaults to `false`, so an apply
keeps the stack (image, secrets, network, and service account) but runs no VM
and costs nothing for compute. To start streaming, set `running` to `true` and
apply. The `logs` output links to the container's logs in Cloud Logging.

To apply from your own machine, copy `terraform/terraform.tfvars.example` to
`terraform/terraform.tfvars`, then:

```bash
cd terraform
tofu init -backend-config="bucket=STATE_BUCKET"
tofu apply
```

### Replacing the VM

An update replaces the VM with no surge: the old VM stops before the new one
starts, because two VMs would send two streams to one key. The broadcast
stays up across the gap, as it does across a preemption.

## Quota

The YouTube Data API gives a project 10,000 units a day by default.

| Call | Units | Default interval | Units a day |
|---|---|---|---|
| `videos.list` (viewer count) | 1 | 60 s | 1,440 |
| `liveChatMessages.list` | 5 | 75 s, or longer when YouTube asks | 5,760 or fewer |
| `search.list` (only with `CHANNEL_ID`, while no broadcast is known) | 100 | 30 min | up to 4,800 |

With `VIDEO_ID` set, a day costs about 7,200 units. After a quota error, the
program stops calling the API for `QUOTA_PAUSE` and keeps streaming with the
last state it read.

## Performance and cost

The budget is $0.10 a minute. CPU use with 10,000 boids and the `veryfast`
preset, measured on an Apple M-series Mac, which is Arm like N4A. The
program and ffmpeg 9.0.2 ran in the linux/arm64 image, limited to 2 CPUs.
All four held real time with no dropped frames:

| Size | Bitrate | Cores |
|---|---|---|
| 1280x720, 30 fps | 4.5 Mbps | 0.55 |
| 1280x720, 60 fps | 7.5 Mbps | 0.9 |
| 1920x1080, 30 fps | 8 Mbps | 0.9 |
| 1920x1080, 60 fps | 12 Mbps | 1.9 (outside the container) |

A Google Cloud vCPU does less work than one of these cores. Terraform
runs 1280x720 at 30 fps on `n4a-highcpu-2`, two Axion cores, which should
leave about half the VM free. For 1920x1080 at 60 fps, set `machine_type`
to `c3d-highcpu-4`, `width` and `height` to 1920 and 1080, `fps` to 60,
and `video_bitrate` to 12000000. The image runs on Arm and x86, and
Terraform picks the boot image and disk type from the machine family.

Spot prices in `us-central1`, for a month of 730 hours:

| Machine | vCPUs | A month |
|---|---|---|
| `n4a-highcpu-2` | 2 | about $17 |
| `c3d-highcpu-4` | 4 | about $26 |
| `c3-highcpu-8` | 8 | about $88 |

The external IP adds about $1.80 a month and the boot disk about $1.
[Data sent to YouTube](https://cloud.google.com/vpc/network-pricing) is free.
Spot prices change as often as daily; check the
[Spot VM pricing](https://cloud.google.com/spot-vms/pricing) page.

## Not yet verified

These parts haven't run against the real services:

- A YouTube Data API key may not be enough for `liveChatMessages.list`. If
  YouTube rejects it, the program needs OAuth credentials for the channel.
- An N4A VM. The stream kept up on 2 Apple M-series cores, which are
  faster than Axion's. Container-Optimized OS for Arm hasn't booted on N4A
  with this template either.
- Container-Optimized OS sending the container's logs to Cloud Logging as
  `cos_containers`.
