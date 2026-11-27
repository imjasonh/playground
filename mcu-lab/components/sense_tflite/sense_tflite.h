#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct sense_tflite_runner sense_tflite_runner_t;

typedef enum {
    SENSE_TFLITE_DTYPE_UNKNOWN = 0,
    SENSE_TFLITE_DTYPE_INT8 = 1,
    SENSE_TFLITE_DTYPE_UINT8 = 2,
    SENSE_TFLITE_DTYPE_FLOAT32 = 3,
} sense_tflite_dtype_t;

typedef struct {
    int32_t dims[4];
    int32_t num_dims;
    sense_tflite_dtype_t input_dtype;
    int32_t num_outputs;
    size_t arena_used_bytes;
} sense_tflite_info_t;

/*
 * Create a TFLite Micro interpreter over `model_data[0..model_len]`.
 *
 * The caller MUST keep `model_data` alive and immutable until
 * `sense_tflite_destroy` is called. Allocates `arena_bytes` from PSRAM
 * (falling back to regular heap). Returns NULL on failure.
 */
sense_tflite_runner_t *sense_tflite_create(
    const uint8_t *model_data,
    size_t model_len,
    size_t arena_bytes,
    sense_tflite_info_t *out_info
);

/*
 * Run inference on an RGB888 (or grayscale) uint8 image buffer matching the
 * model's input tensor element count. Writes dequantized class scores into
 * `out_scores[0..max_scores]` and returns the number of scores written, or < 0
 * on error.
 */
int sense_tflite_invoke_u8_rgb(
    sense_tflite_runner_t *runner,
    const uint8_t *rgb,
    size_t rgb_len,
    float *out_scores,
    size_t max_scores
);

/*
 * Run inference on a float32 input buffer (e.g. a 96x64 log-mel spectrogram
 * patch or 1D audio waveform), automatically quantizing to the input tensor's
 * scale/zero_point if the model is INT8/UINT8. Writes dequantized class scores
 * into `out_scores[0..max_scores]` and returns the number of scores written, or
 * < 0 on error.
 */
int sense_tflite_invoke_f32(
    sense_tflite_runner_t *runner,
    const float *input,
    size_t input_len,
    float *out_scores,
    size_t max_scores
);

void sense_tflite_destroy(sense_tflite_runner_t *runner);

#ifdef __cplusplus
}
#endif
