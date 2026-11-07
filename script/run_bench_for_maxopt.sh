#!/bin/bash
# OptPCSat over a corpus: script/run_bench.sh reading OptPCSat's answer (the last line that
# names a verdict), one run at a time, restarting an aborted run up to twelve times.
exec env para=1 retries=12 reader=optpcsat "$(dirname -- "$0")/run_bench.sh" "$@"
