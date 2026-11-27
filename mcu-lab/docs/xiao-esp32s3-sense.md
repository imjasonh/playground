# Seeed Studio XIAO ESP32-S3 Sense — Recorder & On-Device TFLite Micro Setup

The `xiao-esp32s3-sense` board runs `recorder`, which continuously records
1-minute audio+video `.mov` clips (MJPEG + 16 kHz 16-bit mono PCM) to a microSD
card, evicts the oldest clips when free space drops below headroom, serves clips
over HTTP with byte-range streaming for the Playground iOS app, and tags clips
entirely on device using **TensorFlow Lite Micro (`espressif/esp-tflite-micro`)**
models loaded from the microSD card.

> **TFLite models are required for tagging.** There are no built-in heuristic
> detectors; if `/models/vision.tflite` and `/models/audio.tflite` are not
> present on the SD card, video/audio recording still works, but clips will not
> be tagged (`models: []` in `/api/status` and a warning in the iOS app).

---

## 1. Prepare the microSD Card & Download Pre-Trained Models

Format a microSD card (up to 32 GB recommended) as **FAT32**, then create a
`/models/` directory at the root of the card:

```text
<SD_CARD>/
├── clips/                    # created automatically (clip_000001.mov + clip_000001.json)
└── models/
    ├── vision.tflite         # pre-trained visual classifier (MobileNetV1 INT8/UINT8)
    ├── vision_labels.txt     # ImageNet-1K label map
    ├── audio.tflite          # pre-trained audio classifier (YAMNet INT8 mel-patch)
    └── yamnet_class_map.csv  # (or audio_labels.txt) AudioSet 521-class label map
```

### Download the Recommended Models

Replace `/Volumes/SDCARD` with your mounted SD card path:

```bash
SD="/Volumes/SDCARD"
mkdir -p "$SD/models"

# 1) Visual model: MobileNetV1 0.25 128×128 quantized (~480 KB, ImageNet-1K)
curl -fsSL \
  https://github.com/google-coral/test_data/raw/master/mobilenet_v1_0.25_128_quant.tflite \
  -o "$SD/models/vision.tflite"
curl -fsSL \
  https://github.com/google-coral/test_data/raw/master/imagenet_labels.txt \
  -o "$SD/models/vision_labels.txt"

# 2) Audio model: YAMNet INT8 TFLite-Micro mel-patch (~4.0 MB, 521 AudioSet classes)
curl -fsSL \
  https://huggingface.co/chayuto/yamnet-mel-int8-tflm/resolve/main/yamnet.tflite \
  -o "$SD/models/audio.tflite"
curl -fsSL \
  https://huggingface.co/chayuto/yamnet-mel-int8-tflm/resolve/main/yamnet_class_map.csv \
  -o "$SD/models/yamnet_class_map.csv"
```

You can install both models together, or only one of them (vision-only or
audio-only). Both fit simultaneously in the XIAO ESP32-S3 Sense's 8 MB Octal
PSRAM (~4.5 MB model weights + ~1.7 MB tensor arenas + camera framebuffers).

---

## 2. What the Models Detect

### Visual Model (`vision.tflite` — MobileNetV1 0.25 128×128, ImageNet-1K)
Runs at ~1 Hz on decoded camera frames resized to the model's input tensor
(`128×128×3` RGB888) and records the top classes above 45% confidence.

**1,000 visual classes** trained on ImageNet-1K, including:
- **Birds:** `jay` (blue jay), `robin`, `hummingbird`, `magpie`, `chickadee`,
  `bald eagle`, `goldfinch`, `indigo bunting`, `house finch`, `junco`, `owl`,
  `woodpecker`
- **Dogs (120+ breeds):** `golden retriever`, `labrador retriever`, `beagle`,
  `german shepherd`, `pug`, `poodle`, `chihuahua`, `border collie`, `corgi`,
  `husky`, `boxer`, `dachshund`, etc.
- **Other wildlife & pets:** `tabby`, `persian cat`, `fox squirrel`,
  `cottontail`, `red fox`, `raccoon`, `black bear`
- **Everyday scenes & vehicles:** `bicycle`, `sports car`, `pickup`, `school bus`,
  `backpack`, `umbrella`, etc.

### Audio Model (`audio.tflite` — YAMNet INT8, Google AudioSet)
Computes a 96×64 HTK log-mel spectrogram (16 kHz mono, 25 ms Hann window, 10 ms
hop, 64 mel bands 125–7500 Hz) on device every ~0.48 s and runs YAMNet INT8
inference, recording the top classes above 40% confidence.

**521 audio event classes** trained on Google AudioSet, including:
- **Dogs & pets:** `dog`, `bark`, `yip`, `howl`, `bow-wow`, `growling`,
  `whimper`, `cat`, `purr`, `meow`
- **Birds & nature:** `bird`, `bird vocalization`, `chirp`, `pigeon`, `crow`,
  `caw`, `owl`, `duck`, `goose`, `frog`, `cricket`, `wind`, `rain`, `thunder`
- **Human & household:** `speech`, `conversation`, `laughter`, `baby cry`,
  `cough`, `footsteps`, `doorbell`, `knock`, `glass`, `alarm`, `smoke detector`
- **Vehicles & outdoors:** `car`, `car horn`, `siren`, `motorcycle`,
  `helicopter`, `airplane`, `train`, `lawn mower`, `music`

### Using Your Own `.tflite` Models
You can swap in any quantized (`int8` or `uint8`) or `float32` classification
`.tflite` model without reflashing:
- **Vision:** Any `[1, H, W, 3]` (RGB) or `[1, H, W, 1]` (grayscale) classifier
  whose tensor arena fits within 512 KiB in PSRAM.
- **Audio:** Either a 2D log-mel spectrogram model (`[1, frames, mel_bins]` or
  `[1, frames, mel_bins, 1]`, matching YAMNet's 16 kHz / 25 ms / 10 ms / 125–7500 Hz
  HTK mel frontend) or a 1D normalized 16 kHz waveform model (`[1, samples]`)
  whose tensor arena fits within 1.4 MiB in PSRAM.
- Supported TFLite Micro ops: `Conv2D`, `DepthwiseConv2D`, `FullyConnected`,
  `AveragePool2D`, `MaxPool2D`, `Mean`, `Reshape`, `Quantize`, `Dequantize`,
  `Softmax`, `Logistic`, `Pad`, `Add`, `Mul`, `Sub`, `Relu`, `Relu6`, `Squeeze`,
  `Concatenation`, `ResizeBilinear`, `StridedSlice`, `Transpose`.

---

## 3. Build & Flash Firmware

```bash
espup install --targets esp32,esp32c3,esp32s3
cd mcu-lab

# Optional: join your home Wi-Fi instead of creating SoftAP `XIAO-S3-Sense` (192.168.4.1)
export MCU_LAB_WIFI_SSID="MyWiFi"
export MCU_LAB_WIFI_PASS="MyPassword"

make flash-all BOARD=xiao-esp32s3-sense APP=recorder
make monitor
```

---

## 4. Connect from the Playground iOS App

1. If using SoftAP mode, join Wi-Fi **`XIAO-S3-Sense`** (open AP, IP
   `192.168.4.1`). If using STA mode, ensure your iPhone is on the same Wi-Fi
   network and note the board's IP from `make monitor` or BLE telemetry.
2. Open **Playground → MCU Lab**, enter the board's IP (default `192.168.4.1`),
   and tap **Connect**.
3. The panel displays active TFLite models (`vision:tflite`, `audio:tflite`),
   live detected tags during recording, tag filter chips (e.g. `jay`, `dog`,
   `bark`, `bird`), and one-tap AVPlayer streaming + deletion for every clip.

### HTTP API
- `GET /api/status` — Wi-Fi info, SD free/total space, recording state, loaded `models`, `active_tags`
- `GET /api/tags` — distinct tags with clip counts across all saved clips
- `GET /api/clips` (optional `?tag=<label>`) — clip list with per-clip `tags` (`label`, `source`, `confidence`, `first_s`, `count`)
- `GET /clips/<name>` — HTTP `206 Partial Content` byte-range streaming for `AVPlayer`
- `POST /api/record/start`, `POST /api/record/stop`, `DELETE /api/clips/<name>`
