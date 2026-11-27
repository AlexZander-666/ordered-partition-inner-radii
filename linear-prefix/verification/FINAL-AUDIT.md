# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local project on Linux ARM64. Lean 4.33.1 built all 412 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 412 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separately located, version-locked external dependency cache.

The lexical source scan passed. The 510 source reports and 9 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the original polynomial and the final theorem to the original rows.

- Source ZIP SHA-256 `8d7c301a6f3575a8ee6349d9b2e2e56be48f221e824bd1decc353342e983ca51`
- Entry source SHA-256 `16c51c83c9536d49f3004e87f1578b7c12ca0325f40db5c8053e8f0e565985b4`
- Cold log SHA-256 `4568286ed024624b25c80a70ccf7d0ce9cf43ff270e84b22b8ec1df19be72653`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
