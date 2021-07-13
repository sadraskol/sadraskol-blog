#!/bin/bash

set -x

for file in *.dot; do
  basefile=$(basename $file .dot)
  dot -Tsvg ${file} -o ${basefile}.svg
done
