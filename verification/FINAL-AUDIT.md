# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local project on Linux ARM64. Lean 4.33.1 built all 32 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 32 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separately located, version-locked external dependency cache.

The lexical source scan passed. The 111 source reports and 6 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the sharp nearest-zero limits, the sinc scaling theorem and the logarithmic zero-free disk to the original rows.

- Source ZIP SHA-256 `25c04c59bcceee683fcc2e527730cbfb1bc905507c13eb56be4e69d03790fb47`
- Entry source SHA-256 `ead7be3d1ebf8ab43254f8441790c6e7b8df23aad8aedd5bd31dc7b35aec8ea9`
- Cold log SHA-256 `ec4b6f4c9a34194797d2868af703a391086f3079f4a44c903a9fc0774d909d80`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
