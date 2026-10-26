#!/bin/sh
set -eu
cd "$(dirname "$0")"
nice -n 19 python3.11 s_bench.py
python3.11 census.py
