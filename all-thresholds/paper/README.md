# The nearest complex zeros of ordered set-partition polynomials with a large-block marker

Bowen Zuo, East China University of Science and Technology.

This is the author revision of the article published as version 1.0.0. It includes all fixed thresholds at least two and retains the earlier result for thresholds at least four. [Earlier published version](https://doi.org/10.5281/zenodo.24573157)

Compile main.tex twice with pdfLaTeX. With Python 3 and TeX Live 2026 available, use

    python3 -B reproduce.py

The script rebuilds the same PDF from loose and archived source in two fresh directories. It also regenerates the 30 sign records from the original first-block recurrence using exact integers at dyadic endpoints.

The separate verified Lean archive proves both limiting radii and the locally uniform sinc limit for every fixed threshold j≥2. The top module is OrderedPartitions.CriticalEdgeAllThresholds. The explicit logarithmic bound applies when j≥4 and n≥3. At j=2,3 the exact limiting radii are strict finite-size lower bounds and the deviation is eventually at most L(3π/2)²/n². The project locks Lean and all external dependencies and contains an independent cold build and kernel replay receipt.
