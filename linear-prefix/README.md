# A linear fraction of interlacing inner zeros in ordered set partitions

Bowen Zuo, East China University of Science and Technology.

For each fixed block threshold j ≥ 2 and fixed row-gap bound H ≥ 1,
the original ordered, labelled row has a positive linear prefix of simple
negative roots. The roots are ranked over its entire complex zero set.
For every gap h from 1 through H, the two rows strictly interlace over the
certified prefix, with no ties in absolute-value order.

- [Paper](paper/main.pdf) · [Release v1.2.0](https://github.com/AlexZander-666/ordered-partition-inner-radii/releases/tag/v1.2.0)
- [Locked Lean project and verifier](formal/README.md)
- [Statement map](verification/STATEMENT-MAP.md) · [Scope and reproduction](verification/SCOPE.md) · [Spark audit](verification/FINAL-AUDIT.md)

Run `sha256sum -c SHA256SUMS` from here. Verify the paper from a fresh
extraction of `paper/arxiv-source.zip` using
`python3 -B reproduce.py --output main.pdf --log build.log`.
Set `PDFLATEX` to the absolute path of pdfLaTeX if it is absent from `PATH`.
Matching the author PDF bytes requires its TeX Live 2026 toolchain and fonts.

The formal entry is `OrderedPartitions.CriticalEdgeLinearPrefix` and the
main declaration is `OrderedPartitions.CriticalEdge.original_linear_prefix`.
The archived Spark receipt covers 412 local modules, 412 separate Lean
kernel processes, 510 source axiom reports and nine targeted reports.
Follow `formal/README.md` to rebuild against the locked dependencies.

The fixed-scale sinc and nearest-distance results are in the companion
[paper and proof, v1.1.0](https://github.com/AlexZander-666/ordered-partition-inner-radii/releases/tag/v1.1.0).
Apache-2.0 covers this project's original Lean and verification software.
Bowen Zuo retains copyright in the manuscript and TeX.
