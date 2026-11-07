#!/bin/bash
# One run of the table run_corpus.sh reads; generated from its row.
exec "$(dirname -- "$0")/../run_corpus.sh" popl2023mod muval_ppm_popl27_no_ad_300
