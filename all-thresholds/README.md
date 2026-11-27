# Inner radii at every ordered block threshold

Bowen Zuo, East China University of Science and Technology.

This edition of *The nearest complex zeros of ordered set-partition
polynomials with a large-block marker* proves both limiting radii and
locally uniform sinc scaling for every fixed threshold j ≥ 2. It includes
the sharp strict barrier and eventual inverse-quadratic estimate at
j = 2, 3, and retains the explicit logarithmic bound for j ≥ 4.

- [Version 1.1.0 release](https://github.com/AlexZander-666/ordered-partition-inner-radii/releases/tag/v1.1.0)
- [Paper](paper/main.pdf) · [TeX and exact-sample replay](paper/README.md)
- [Locked Lean proof and clean build instructions](formal/README.md)
- [Original-object statement map](verification/STATEMENT-MAP.md) · [Cold Spark audit](verification/FINAL-AUDIT.md)
- [Changes from v1.0.0](verification/REVISION.md)

From this directory, verify the archived files with:

    sha256sum -c SHA256SUMS

From `paper/`, run `python3 -B reproduce.py` with pdfLaTeX.
The script builds the paper from loose sources and from its TeX ZIP,
and replays the 30 exact sign brackets. The full formal entry is
`OrderedPartitions.CriticalEdgeAllThresholds`. To rebuild it independently,
use the instructions for `formal/verify.py` with the
separate, pinned external dependencies. The Spark receipt records 394
strict source builds and independent kernel processes, 452 source
axiom reports, and 10 additional targeted declarations.

The original fixed-threshold-range release remains available at
[GitHub v1.0.0](https://github.com/AlexZander-666/ordered-partition-inner-radii/releases/tag/v1.0.0)
and [Zenodo](https://doi.org/10.5281/zenodo.24573157).
Apache-2.0 covers the original Lean source and verification scripts.
The author retains copyright in the manuscript.
