#!/bin/bash
THING=
FOO=hi
PATH=/tmp/x

if [ -z $THING ]; then  # want "unquoted $VAR in [ ] test"
    echo empty
fi

if [ -z "$THING" ]; then
    echo quoted
fi

if [ -n $FOO ]; then  # want "unquoted $VAR in [ ] test"
    echo set
fi

if [ -f $PATH ]; then  # want "unquoted $VAR in [ ] test"
    echo file
fi
