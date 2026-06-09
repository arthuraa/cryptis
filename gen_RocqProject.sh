#!/bin/sh
set -e
# Script generating the contents of [_RocqProject] based on files [config/*].

echo "# Generated file, edit [config/*] instead."

echo
echo "# Search paths"
# Adding "-Q " prefix to all non-empty, non-comment lines of [config/paths].
cat config/paths | grep "^[^#]\+" | sed "s/^/-Q /"

echo
echo "# Flags"
# Adding "-arg " prefix to all non-empty, non-comment lines of [config/flags].
cat config/flags | grep "^[^#]\+" | sed "s/^/-arg /"

# List of source files.
echo
echo "# Sources"
# Take only non-empty, non-comment lines of [config/source-list].
cat config/source-list | grep "^[^#]\+"
