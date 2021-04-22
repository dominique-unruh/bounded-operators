#!/bin/bash

# Runs a locally installed Isabelle

set -e

ISABELLE_DIR=/opt/Isabelle2021

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/All.thy" "$ISABELLE_DIR/src/Pure/ROOT.ML")
else
    FILES=()
fi

"$ISABELLE_DIR"/bin/isabelle jedit -l Bounded_Operators-Prerequisites -d "$DIR" "$@" "${FILES[@]}" &
