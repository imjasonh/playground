#include "sense_tflite.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>

#include "esp_heap_caps.h"
#include "tensorflow/lite/micro/micro_interpreter.h"
#include "tensorflow/lite/micro/micro_mutable_op_resolver.h"
#if __has_include("tensorflow/lite/schema/schema_generated.h")
#include "tensorflow/lite/schema/schema_generated.h"
#elif __has_include("tensorflow/compiler/mlir/lite/schema/schema_generated.h")
#include "tensorflow/compiler/mlir/lite/schema/schema_generated.h"
#endif

namespace {

using SenseOpResolver = tflite::MicroMutableOpResolver<24>;

TfLiteStatus register_ops(SenseOpResolver &resolver) {
    if (resolver.AddConv2D() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddDepthwiseConv2D() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddFullyConnected() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddAveragePool2D() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddMaxPool2D() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddMean() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddReshape() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddQuantize() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddDequantize() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddSoftmax() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddLogistic() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddPad() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddAdd() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddMul() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddSub() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddRelu() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddRelu6() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddSqueeze() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddConcatenation() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddResizeBilinear() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddStridedSlice() != kTfLiteOk) return kTfLiteError;
    if (resolver.AddTranspose() != kTfLiteOk) return kTfLiteError;
    return kTfLiteOk;
}

sense_tflite_dtype_t map_dtype(TfLiteType t) {
    switch (t) {
        case kTfLiteInt8:
            return SENSE_TFLITE_DTYPE_INT8;
        case kTfLiteUInt8:
            return SENSE_TFLITE_DTYPE_UINT8;
        case kTfLiteFloat32:
            return SENSE_TFLITE_DTYPE_FLOAT32;
        default:
            return SENSE_TFLITE_DTYPE_UNKNOWN;
    }
}

size_t tensor_element_count(const TfLiteTensor *t) {
    if (!t || !t->dims) return 0;
    size_t count = 1;
    for (int i = 0; i < t->dims->size; ++i) {
        if (t->dims->data[i] <= 0) return 0;
        count *= static_cast<size_t>(t->dims->data[i]);
    }
    return count;
}

int read_output_scores(const TfLiteTensor *out, float *out_scores, size_t max_scores) {
    if (!out || !out_scores) return -1;
    size_t n = tensor_element_count(out);
    if (n == 0) return -2;
    size_t count = std::min(n, max_scores);
    float scale = out->params.scale;
    int32_t zp = out->params.zero_point;

    switch (out->type) {
        case kTfLiteUInt8: {
            const uint8_t *src = out->data.uint8;
            if (scale > 0.0f) {
                for (size_t i = 0; i < count; ++i) {
                    out_scores[i] = static_cast<float>(static_cast<int32_t>(src[i]) - zp) * scale;
                }
            } else {
                for (size_t i = 0; i < count; ++i) {
                    out_scores[i] = static_cast<float>(src[i]) / 255.0f;
                }
            }
            return static_cast<int>(count);
        }
        case kTfLiteInt8: {
            const int8_t *src = out->data.int8;
            float eff_scale = scale > 0.0f ? scale : (1.0f / 255.0f);
            for (size_t i = 0; i < count; ++i) {
                out_scores[i] = static_cast<float>(static_cast<int32_t>(src[i]) - zp) * eff_scale;
            }
            return static_cast<int>(count);
        }
        case kTfLiteFloat32: {
            std::memcpy(out_scores, out->data.f, count * sizeof(float));
            return static_cast<int>(count);
        }
        default:
            return -3;
    }
}

}  // namespace

struct sense_tflite_runner {
    uint8_t *arena = nullptr;
    size_t arena_bytes = 0;
    SenseOpResolver resolver;
    tflite::MicroInterpreter *interpreter = nullptr;
};

extern "C" {

sense_tflite_runner_t *sense_tflite_create(
    const uint8_t *model_data,
    size_t model_len,
    size_t arena_bytes,
    sense_tflite_info_t *out_info
) {
    if (!model_data || model_len < 16 || arena_bytes < 4096) {
        return nullptr;
    }

    const tflite::Model *model = tflite::GetModel(model_data);
    if (!model) {
        return nullptr;
    }
#ifdef TFLITE_SCHEMA_VERSION
    if (model->version() != TFLITE_SCHEMA_VERSION) {
        return nullptr;
    }
#endif

    auto *runner = new (std::nothrow) sense_tflite_runner();
    if (!runner) {
        return nullptr;
    }

    if (register_ops(runner->resolver) != kTfLiteOk) {
        delete runner;
        return nullptr;
    }

    runner->arena = static_cast<uint8_t *>(
        heap_caps_malloc(arena_bytes, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT)
    );
    if (!runner->arena) {
        runner->arena = static_cast<uint8_t *>(std::malloc(arena_bytes));
    }
    if (!runner->arena) {
        delete runner;
        return nullptr;
    }
    runner->arena_bytes = arena_bytes;

    runner->interpreter = new (std::nothrow) tflite::MicroInterpreter(
        model,
        runner->resolver,
        runner->arena,
        runner->arena_bytes
    );
    if (!runner->interpreter) {
        heap_caps_free(runner->arena);
        delete runner;
        return nullptr;
    }

    if (runner->interpreter->AllocateTensors() != kTfLiteOk) {
        delete runner->interpreter;
        heap_caps_free(runner->arena);
        delete runner;
        return nullptr;
    }

    if (out_info) {
        std::memset(out_info, 0, sizeof(*out_info));
        TfLiteTensor *in = runner->interpreter->input(0);
        TfLiteTensor *out = runner->interpreter->output(0);
        if (in && in->dims) {
            out_info->num_dims = std::min(in->dims->size, 4);
            for (int i = 0; i < out_info->num_dims; ++i) {
                out_info->dims[i] = in->dims->data[i];
            }
            out_info->input_dtype = map_dtype(in->type);
        }
        out_info->num_outputs = static_cast<int32_t>(tensor_element_count(out));
        out_info->arena_used_bytes = runner->interpreter->arena_used_bytes();
    }

    return runner;
}

int sense_tflite_invoke_u8_rgb(
    sense_tflite_runner_t *runner,
    const uint8_t *rgb,
    size_t rgb_len,
    float *out_scores,
    size_t max_scores
) {
    if (!runner || !runner->interpreter || !rgb || !out_scores) return -1;
    TfLiteTensor *in = runner->interpreter->input(0);
    if (!in) return -2;
    size_t expected = tensor_element_count(in);
    if (expected == 0 || rgb_len < expected) return -3;

    switch (in->type) {
        case kTfLiteUInt8:
            std::memcpy(in->data.uint8, rgb, expected);
            break;
        case kTfLiteInt8: {
            float scale = in->params.scale;
            int32_t zp = in->params.zero_point;
            if (scale > 0.0f) {
                for (size_t i = 0; i < expected; ++i) {
                    float norm = static_cast<float>(rgb[i]) / 255.0f;
                    int32_t q = static_cast<int32_t>(std::lroundf(norm / scale)) + zp;
                    q = std::max<int32_t>(-128, std::min<int32_t>(127, q));
                    in->data.int8[i] = static_cast<int8_t>(q);
                }
            } else {
                for (size_t i = 0; i < expected; ++i) {
                    in->data.int8[i] = static_cast<int8_t>(static_cast<int32_t>(rgb[i]) - 128);
                }
            }
            break;
        }
        case kTfLiteFloat32:
            for (size_t i = 0; i < expected; ++i) {
                in->data.f[i] = static_cast<float>(rgb[i]) / 255.0f;
            }
            break;
        default:
            return -4;
    }

    if (runner->interpreter->Invoke() != kTfLiteOk) return -5;
    return read_output_scores(runner->interpreter->output(0), out_scores, max_scores);
}

int sense_tflite_invoke_f32(
    sense_tflite_runner_t *runner,
    const float *input,
    size_t input_len,
    float *out_scores,
    size_t max_scores
) {
    if (!runner || !runner->interpreter || !input || !out_scores) return -1;
    TfLiteTensor *in = runner->interpreter->input(0);
    if (!in) return -2;
    size_t expected = tensor_element_count(in);
    if (expected == 0 || input_len < expected) return -3;

    float scale = in->params.scale;
    int32_t zp = in->params.zero_point;

    switch (in->type) {
        case kTfLiteInt8: {
            float inv_scale = scale > 0.0f ? (1.0f / scale) : 1.0f;
            for (size_t i = 0; i < expected; ++i) {
                int32_t q = static_cast<int32_t>(std::lroundf(input[i] * inv_scale)) + zp;
                q = std::max<int32_t>(-128, std::min<int32_t>(127, q));
                in->data.int8[i] = static_cast<int8_t>(q);
            }
            break;
        }
        case kTfLiteUInt8: {
            float inv_scale = scale > 0.0f ? (1.0f / scale) : 1.0f;
            for (size_t i = 0; i < expected; ++i) {
                int32_t q = static_cast<int32_t>(std::lroundf(input[i] * inv_scale)) + zp;
                q = std::max<int32_t>(0, std::min<int32_t>(255, q));
                in->data.uint8[i] = static_cast<uint8_t>(q);
            }
            break;
        }
        case kTfLiteFloat32:
            std::memcpy(in->data.f, input, expected * sizeof(float));
            break;
        default:
            return -4;
    }

    if (runner->interpreter->Invoke() != kTfLiteOk) return -5;
    return read_output_scores(runner->interpreter->output(0), out_scores, max_scores);
}

void sense_tflite_destroy(sense_tflite_runner_t *runner) {
    if (!runner) return;
    delete runner->interpreter;
    if (runner->arena) {
        heap_caps_free(runner->arena);
    }
    delete runner;
}

}  // extern "C"
