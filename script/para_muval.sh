#!/bin/bash
# Race muval_prove against muval_disprove on one input; paths stay relative to the caller's repository root.
exec python3 "$(dirname -- "${BASH_SOURCE[0]}")/parallel_muval.py" muval "$@"
