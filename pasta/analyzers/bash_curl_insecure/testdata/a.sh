#!/bin/bash
curl -k https://example.com      # want "disables TLS verification"
curl --insecure https://x.test   # want "disables TLS verification"
curl https://example.com         # OK
