# The nearest complex zeros of ordered set-partition polynomials with a large-block marker

Bowen Zuo, East China University of Science and Technology.

For each fixed threshold \(j\ge4\), the paper identifies the limiting
distances of the full complex zero set from \(0\) and \(1\). It proves
locally uniform convergence to \(\sin(\sqrt u)/\sqrt u\) in a window
of width \(n^{-2}\) and an explicit one-sided error of order
\((\log n)/n\) for the inner radii.

- [Paper](paper/main.pdf) and [TeX build instructions](paper/README.md)
- [Locked Lean build and independent kernel replay](formal/README.md)
- [Theorem map](verification/STATEMENT-MAP.md) and [source pins](verification/SOURCE-PINS.md)
- [Spark source-cold verification](verification/FINAL-AUDIT.md)

Run the published project's exact checks with Python 3. The LaTeX
reproducer run from \`paper/\` recompiles the PDF and regenerates the
frozen exact finite signs. See \`formal/verify.py\` for the Lean commands
and \`.github/workflows/verify.yml\` for the corresponding hosted job.
The Spark receipt records 32 strict source builds, 32 independent
kernel replays, 111 source and six targeted transitive axiom reports.
The full complex zero set appears in the formal theorem.

Apache-2.0 covers the original Lean proof and verification code.
The author retains copyright in the manuscript.
