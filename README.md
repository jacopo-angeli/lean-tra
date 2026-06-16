# lean-tra

Lean 4 formalization of **Term Relation Algebras** (TRAs), introduced by
F. Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026.
The thesis goal is to mechanically verify the **Bridge Theorem (Thm. 37)** and
its three corollaries — confluence of reduction, determinism of evaluation,
congruence of bisimilarity — and to instantiate them on a concrete syntax
(λ-calculus).

## Status

Scaffold complete for layers 1–8; instances (layer 9) are placeholders.
No proof closed yet; every `sorry` is annotated with a `-- deps: …` line
listing the expected dependencies.

| Layer | Objects                          | Files                                      | Status                |
| ----- | -------------------------------- | ------------------------------------------ | --------------------- |
| 0     | P1–P4 Prerequisites              | (Mathlib)                                  | external              |
| 1     | A1–A4 Allegory / Relator         | `Allegory/{Basic,…,Relator/*}.lean`        | scaffold              |
| 2     | T1 TRA                           | `Allegory/TRA/Basic.lean`                  | scaffold              |
| 3     | E1–E3, H1 Expressiveness         | `Allegory/TRA/{Properties,Modalities,…}`   | scaffold              |
| 4     | O1–O4 Operational decomposition  | `Allegory/TRA/Operational/*`               | scaffold              |
| 5     | R1–R5 Reduction                  | `Allegory/TRA/Reduction{,/}*`              | scaffold              |
| 6     | B1–B4 Evaluation                 | `Allegory/TRA/Evaluation/*`                | scaffold              |
| 7     | S1–S4 Similarity                 | `Allegory/TRA/Similarity/*`                | scaffold (S3 dormant) |
| 8     | M1–M2 Bridge Theorem             | `Allegory/TRA/Bridge{,/}*`                 | scaffold              |
| 9     | I1–I7 λ-calculus                 | `Allegory/Instances/Lambda/*`              | placeholder           |

Complete object ↔ file ↔ paper ↔ dependency ↔ sorry-count map:
see [`benchmark.csv`](./benchmark.csv).

## Build

```bash
lake build Allegory                # root + transitive closure
lake build Allegory.TRA.Bridge     # Bridge Theorem and its dependencies only
```

Cold build (assuming Mathlib in cache): ~10 minutes. Expected warnings:
only `declaration uses sorry`.

Quick health checks:
```bash
# Active sorry count (excludes commented '-- sorry' tokens).
grep -rE '^\s*sorry\s*$' Allegory --include='*.lean' | wc -l

# Residual proof-sketch markers (must be 0).
grep -r -- '-- ?' Allegory --include='*.lean' | wc -l
```

## Repo layout

```
Allegory.lean                # Root index: imports every public module
Allegory/
├── Basic.lean               # A1 Allegory (Freyd–Scedrov §2.11)
├── Distributive.lean        # A2 DistributiveAllegory
├── Division.lean            # A3 DivisionAllegory (unused downstream — see TODO)
├── LocallyComplete.lean     # A4 LocallyCompleteAllegory (= RA in the paper)
├── Relator/
│   ├── Basic.lean           # ColaxRelator / Semirelator / Relator + ω-cocont.
│   └── Cocartesian.lean     # Cocartesian decomposition (Def. 5)
├── TRA/
│   ├── Basic.lean           # T1 TRA class (Def. 6)
│   ├── Properties.lean      # E1 Compatible / CUI / Substitutive / Leibniz
│   ├── Modalities.lean      # E2 □ / ♦ / ♢ / Closed (§3.2.1)
│   ├── FixedPointLemmas.lean # E3 Lemma 16
│   ├── Harmony.lean         # H1 Harmony axiom (under review)
│   ├── Operational/         # O1–O4
│   ├── Reduction/           # R1–R4 + Reduction.lean (R5)
│   ├── Evaluation/          # B1–B4
│   ├── Similarity/          # S1–S4
│   └── Bridge/Lemma36.lean + Bridge.lean   # M1, M2
└── Instances/
    ├── FirstOrder/TRA.lean
    └── Lambda/{Terms,Operational,Beta,Confluence}.lean
docs/                        # paper + appendix (gitignored)
logs/                        # session work logs
benchmark.csv                # objects ↔ files ↔ paper refs ↔ deps
CLAUDE.md                    # session conventions and protocols for the assistant
```

## Known TODOs (for the supervisor meeting)

- **Allegory hierarchy decision**: A3 (`DivisionAllegory`) is unused downstream.
  Three options: (a) keep it for a possible standalone Mathlib contribution;
  (b) collapse to `LocallyCompleteAllegory` as the paper does; (c) keep and
  motivate.
- **`leftResidual` / `bisimilarity`** in `TRA/Similarity/Basic.lean` are still
  `def := sorry` — replace with proper `sSup` / `gfp` definitions. (Three
  inline `(sorry : X ⟶ X)` casts in `Theorem35.lean` and `Bridge.lean`
  disappear automatically once `bisimilarity` is defined.)
- **S3 (`Congruence.lean`) is dormant**: the file body is fully commented.
  Convert to honest stubs or delete.
- **Kleene star** is redefined locally in three files
  (`Reduction/Confluence`, `Reduction/Parallel`, `Evaluation/BigStep`):
  consolidate into `LocallyComplete.lean`.
- **Paper notation**: add `Allegory/Notation.lean` with `scoped notation` for
  `aᴴ`, `a⇛`, `aᴱ`, `a⇓`, `a§`, etc.
- **Instances (layer 9)**: all placeholders. First vertical-slice candidate:
  combinatory logic (Example 18 in the paper).

## References

- F. Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026
  (primary reference; copy not committed in `docs/`).
- P. J. Freyd, A. Scedrov, *Categories, Allegories*, 1990 (§2.11–2.31 for
  the allegorical scaffolding).
- D. Howe, *Proving congruence of bisimulation in functional programming
  languages*, 1996 (Howe's method, reused in S2/S3/S4).
- F. Gavazzo, *On a Term Relation Algebra Approach to Term Rewriting*, 2023
  (precursor proceedings with more detailed proofs; copy not committed in
  `docs/`).
