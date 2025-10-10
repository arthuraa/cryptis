#!/bin/bash

make clean
make RocqMakefile

rm -f table.tex

cat >> table.tex <<EOF
\begin{tabular}{r|l|l|l|l|l}
\toprule
Component & Implementation (loc) & Proofs (loc) & Game (loc) & Everything (loc) & Wall-clock time (s) \\\\
\midrule
EOF

echo "Core"

./example_stats.sh "Cryptis Core" table.tex \
     cryptis

echo "NSL"

./example_stats.sh "NSL (\\Cref{sec:nsl})" table.tex \
     examples/nsl

echo "ISO"

./example_stats.sh "ISO (\\Cref{sec:iso})" table.tex \
     examples/iso_dh

echo "Connections"

./example_stats.sh "Connections (\\Cref{sec:reliable-connections})" table.tex \
     examples/conn

echo "RPC"

./example_stats.sh "RPC (\\Cref{sec:rpc})" table.tex \
     examples/rpc

echo "Store"

./example_stats.sh "Store (\\Cref{sec:key-value-auth})" table.tex \
     examples/store

cat >> table.tex <<EOF
\bottomrule
\end{tabular}
EOF
