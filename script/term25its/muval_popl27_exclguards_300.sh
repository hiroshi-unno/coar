#!/bin/bash
# One run of the table run_corpus.sh reads; generated from its row.
exec "$(dirname -- "$0")/../run_corpus.sh" term25its muval_popl27_exclguards_300
