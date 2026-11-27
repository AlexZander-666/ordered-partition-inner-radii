# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local project on Linux ARM64. Lean 4.33.1 built all 394 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 394 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separately located, version-locked external dependency cache.

The lexical source scan passed. The 452 source reports and 10 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps both nearest-zero limits and the sinc scaling theorem at all thresholds, and the strict finite-rank wall at thresholds two and three to the original rows.

- Source ZIP SHA-256 `6178f8a9399a72c18891eb9ff4bc049ced553efd57a290c781edcbfab49efa7b`
- Entry source SHA-256 `4a5af93c6d4557a2d3561b7aeff794b1468c84d8d183cf2fe9ee1a87778b4b09`
- Cold log SHA-256 `a674a51faa3564601dbd1939b9fb72800420564a859594c65a21293d6b5464c8`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
