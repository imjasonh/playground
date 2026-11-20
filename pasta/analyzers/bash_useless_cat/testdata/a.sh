#!/bin/bash

# Good: valid cat usages
cat file1 file2 > combined.txt
cat <<EOF
hello
EOF

# Bad: cat in pipeline
cat file.txt | grep "pattern" # want "useless use of cat in pipeline"
cat log.txt | head -n 5 # want "useless use of cat in pipeline"
