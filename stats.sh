#!/bin/bash

#!/bin/bash

if [ $# -ne 1 ]; then
  MAKEJ=1
else
  MAKEJ=$1
fi

make clean
make RocqMakefile

rm -f table.tex

cat >> table.tex <<EOF
\begin{tabular}{r|l|l|l|l|l}
\toprule
Component & Impl. (loc) & Proofs (loc) & Game (loc) & Total (loc) & Wall-clock time (s) \\\\
\midrule
EOF

echo "Core"

./example_stats.sh "Cryptis Core" table.tex \
     cryptis $MAKEJ

echo "NSL"

./example_stats.sh "NSL (\\Cref{sec:nsl})" table.tex \
     examples/nsl $MAKEJ

echo "ISO"

./example_stats.sh "ISO (\\Cref{sec:iso})" table.tex \
     examples/iso_dh $MAKEJ

echo "Connections"

./example_stats.sh "Connections (\\Cref{sec:reliable-connections})" table.tex \
     examples/conn $MAKEJ

echo "RPC"

./example_stats.sh "RPC (\\Cref{sec:rpc})" table.tex \
     examples/rpc $MAKEJ

echo "Store"

./example_stats.sh "Store (\\Cref{sec:key-value-auth})" table.tex \
     examples/store $MAKEJ

cat >> table.tex <<EOF
\bottomrule
\end{tabular}
EOF
