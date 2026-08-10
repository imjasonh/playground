// inkbot-esp32 — poll a Cloudflare Worker for a 800×480 B/W PNG and show it
// on the Waveshare 7.5″ e-Paper panel driven by the official ESP32 board.
//
// Hardware (same as the earlier e-ink SSH prototype, without OTA/SSH):
//   - Waveshare e-Paper ESP32 Driver Board
//   - Waveshare 7.5″ raw mono 800×480 (V2 / UC8179)
//   Fixed pins: SCLK=13 MOSI=14 CS=15 DC=27 RST=26 BUSY=25

#include <Arduino.h>
#include <HTTPClient.h>
#include <PNGdec.h>
#include <Preferences.h>
#include <WiFi.h>
#include <WiFiClientSecure.h>

#include <GxEPD2_BW.h>

#include <vector>

#include "config.h"

// GxEPD2 driver for the modern 800×480 V2 panel. Page height is a quarter of
// the panel so the buffered drawing path stays small; full-frame updates go
// through writeImage() into our own 48 KB packed buffer below.
GxEPD2_BW<GxEPD2_750_T7, GxEPD2_750_T7::HEIGHT / 4> display(
    GxEPD2_750_T7(/*CS=*/15, /*DC=*/27, /*RST=*/26, /*BUSY=*/25));

static Preferences prefs;
static String lastEtag;
static PNG png;

// Packed 1-bit framebuffer (800/8 * 480 = 48000). 1 = white, 0 = black —
// matching both our Worker PNG and GxEPD2's writeImage convention.
static uint8_t frameBuf[GxEPD2_750_T7::WIDTH * GxEPD2_750_T7::HEIGHT / 8];

static bool wifiConnect() {
  WiFi.mode(WIFI_STA);
  WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
  Serial.printf("wifi: connecting to %s", WIFI_SSID);
  const uint32_t start = millis();
  while (WiFi.status() != WL_CONNECTED) {
    if (millis() - start > 30000) {
      Serial.println("\nwifi: timeout");
      return false;
    }
    delay(400);
    Serial.print('.');
  }
  Serial.printf("\nwifi: connected, ip=%s\n", WiFi.localIP().toString().c_str());
  return true;
}

static int32_t pngDraw(PNGDRAW *pDraw) {
  // PNGdec delivers one decoded line. For 1-bit grayscale source, pDraw->pPixels
  // is already packed 1 bpp (MSB first, 1 = white) when PNG_PIXEL_GRAYSCALE.
  // For 8-bit gray we threshold; for RGB we luma-threshold.
  const int y = pDraw->y;
  if (y < 0 || y >= (int)GxEPD2_750_T7::HEIGHT) {
    return 1;
  }
  uint8_t *dest = frameBuf + y * (GxEPD2_750_T7::WIDTH / 8);

  if (pDraw->iBpp == 1) {
    memcpy(dest, pDraw->pPixels, GxEPD2_750_T7::WIDTH / 8);
    return 1;
  }

  memset(dest, 0x00, GxEPD2_750_T7::WIDTH / 8);
  for (int x = 0; x < (int)GxEPD2_750_T7::WIDTH; x++) {
    uint8_t lum;
    if (pDraw->iBpp == 8) {
      lum = pDraw->pPixels[x];
    } else if (pDraw->iBpp == 24) {
      const uint8_t *px = pDraw->pPixels + x * 3;
      lum = (uint8_t)((px[0] * 30 + px[1] * 59 + px[2] * 11) / 100);
    } else if (pDraw->iBpp == 32) {
      const uint8_t *px = pDraw->pPixels + x * 4;
      lum = (uint8_t)((px[0] * 30 + px[1] * 59 + px[2] * 11) / 100);
    } else {
      lum = 255;
    }
    if (lum >= 128) {
      dest[x / 8] |= (uint8_t)(0x80 >> (x & 7));
    }
  }
  return 1;
}

static bool decodePngToFrame(const uint8_t *data, int32_t len) {
  if (png.openRAM((uint8_t *)data, len, pngDraw) != PNG_SUCCESS) {
    Serial.println("png: open failed");
    return false;
  }
  if (png.getWidth() != (int)GxEPD2_750_T7::WIDTH ||
      png.getHeight() != (int)GxEPD2_750_T7::HEIGHT) {
    Serial.printf("png: bad size %dx%d\n", png.getWidth(), png.getHeight());
    png.close();
    return false;
  }
  memset(frameBuf, 0xFF, sizeof(frameBuf)); // white
  if (png.decode(nullptr, 0) != PNG_SUCCESS) {
    Serial.println("png: decode failed");
    png.close();
    return false;
  }
  png.close();
  return true;
}

static void showFrame() {
  // Full-screen write of the packed 1-bit buffer, then one full refresh.
  display.setFullWindow();
  display.writeImage(frameBuf, 0, 0, GxEPD2_750_T7::WIDTH, GxEPD2_750_T7::HEIGHT);
  display.refresh();
  display.hibernate();
  Serial.println("display: refreshed");
}

static void showMessage(const char *msg) {
  display.setRotation(0);
  display.setFullWindow();
  display.firstPage();
  do {
    display.fillScreen(GxEPD_WHITE);
    display.setTextColor(GxEPD_BLACK);
    display.setTextSize(2);
    display.setCursor(24, 220);
    display.print(msg);
  } while (display.nextPage());
  display.hibernate();
}

struct FetchResult {
  int status = 0;
  String etag;
  std::vector<uint8_t> body;
};

static FetchResult fetchImage() {
  FetchResult out;
  WiFiClientSecure client;
  // Prototype: skip cert pinning. Swap for setCACert / bundle for production.
  client.setInsecure();
  client.setTimeout(20);

  HTTPClient http;
  const String url = String(INKBOT_BASE_URL) + "/image.png";
  if (!http.begin(client, url)) {
    Serial.println("http: begin failed");
    return out;
  }
  http.setTimeout(20000);
  http.addHeader("User-Agent", "inkbot-esp32/1.0");
  if (lastEtag.length() > 0) {
    http.addHeader("If-None-Match", lastEtag);
  }
  const char *collect[] = {"ETag", "etag"};
  http.collectHeaders(collect, 2);

  const int code = http.GET();
  out.status = code;
  if (code == 304) {
    Serial.println("http: 304 not modified");
    http.end();
    return out;
  }
  if (code != 200) {
    Serial.printf("http: GET failed, status=%d\n", code);
    http.end();
    return out;
  }

  out.etag = http.header("ETag");
  if (out.etag.isEmpty()) {
    out.etag = http.header("etag");
  }
  const int len = http.getSize();
  WiFiClient *stream = http.getStreamPtr();
  out.body.reserve(len > 0 ? len : 8192);
  uint8_t buf[1024];
  while (http.connected() || stream->available()) {
    const size_t n = stream->available();
    if (n == 0) {
      delay(1);
      continue;
    }
    const size_t got = stream->readBytes(buf, n > sizeof(buf) ? sizeof(buf) : n);
    out.body.insert(out.body.end(), buf, buf + got);
    if (out.body.size() > 256 * 1024) {
      Serial.println("http: body too large");
      out.status = -1;
      out.body.clear();
      break;
    }
  }
  http.end();
  Serial.printf("http: got %u bytes, etag=%s\n", (unsigned)out.body.size(),
                out.etag.c_str());
  return out;
}

static void pollOnce() {
  if (WiFi.status() != WL_CONNECTED) {
    if (!wifiConnect()) {
      return;
    }
  }

  FetchResult got = fetchImage();
  if (got.status == 304) {
    return;
  }
  if (got.status != 200 || got.body.empty()) {
    return;
  }
  if (!decodePngToFrame(got.body.data(), (int32_t)got.body.size())) {
    Serial.println("png: rejected");
    return;
  }
  showFrame();
  if (got.etag.length() > 0) {
    lastEtag = got.etag;
    prefs.putString("etag", lastEtag);
  }
}

void setup() {
  Serial.begin(115200);
  delay(200);
  Serial.println("\ninkbot-esp32: boot");

  SPI.begin(13, /*MISO*/ -1, 14, 15);
  display.init(115200, true, 2, false);
  display.setRotation(0);

  prefs.begin("inkbot", false);
  lastEtag = prefs.getString("etag", "");
  Serial.printf("nvs: last etag=%s\n", lastEtag.c_str());

  if (!wifiConnect()) {
    showMessage("WiFi failed");
  } else {
    showMessage("inkbot ready");
    pollOnce();
  }
}

void loop() {
  delay(POLL_INTERVAL_MS);
  pollOnce();
}
