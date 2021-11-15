#!/bin/bash

# Runs a locally installed Isabelle

set -e

#ISABELLE_DIR=~/svn/isabelle
ISABELLE_DIR=/opt/Isabelle2021-1-RC3

DIR="$(dirname "$BASH_SOURCE[0]")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/All.thy" "$ISABELLE_DIR/src/Pure/ROOT.ML")
else
    FILES=()
fi

#SESSION=Lots-Of-Stuff
SESSION=Complex_Bounded_Operators-Prerequisites

"$ISABELLE_DIR"/bin/isabelle jedit -l "$SESSION" -d "$DIR" "$@" "${FILES[@]}" &
