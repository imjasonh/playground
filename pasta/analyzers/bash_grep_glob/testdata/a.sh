#!/bin/bash
grep '*foo*' file.txt  # want "grep pattern looks like a glob"
grep "*bar*" file.txt  # want "grep pattern looks like a glob"
grep foo file.txt
grep 'foo' file.txt
