idf_component_register(
    SRCS "sense_tflite.cc"
    INCLUDE_DIRS "."
    PRIV_REQUIRES espressif__esp-tflite-micro
)
