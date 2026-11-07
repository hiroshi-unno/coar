#!/bin/bash
# One run of the table run_corpus.sh reads; generated from its row.
exec "$(dirname -- "$0")/../run_corpus.sh" sygus19inv spacer_600
