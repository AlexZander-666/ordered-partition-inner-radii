# The nearest complex zeros of ordered set-partition polynomials with a large-block marker

Bowen Zuo, East China University of Science and Technology.

Compile main.tex twice with pdfLaTeX. With Python 3 and TeX Live 2026 available, python3 -B reproduce.py rebuilds the PDF from loose source and the extracted ZIP, compares their bytes, and independently regenerates the archived exact signs from the first-block recurrence. The dyadic endpoints are proposals. Signs at those endpoints use exact integer arithmetic.

The separate Lean source archive proves the two limiting radii, the locally uniform sinc limit and the finite logarithmic lower bound for every fixed j ≥ 4. Its top module is OrderedPartitions.CriticalEdgeInnerRadii. The development uses Lean and Mathlib revisions identified in lean-toolchain and lake-manifest.json. Its source verifier builds from a fresh directory and replays every local module with the Lean kernel.
