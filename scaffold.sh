#!/bin/bash
set -euo pipefail

# ── directories ──────────────────────────────────────────────────────────────

mkdir -p CategoryTheory/Allegory/Relator
mkdir -p CategoryTheory/Allegory/TRA/Operational
mkdir -p CategoryTheory/Allegory/TRA/Reduction
mkdir -p CategoryTheory/Allegory/TRA/Evaluation
mkdir -p CategoryTheory/Allegory/TRA/Similarity
mkdir -p Instances/FirstOrder
mkdir -p Instances/Lambda
mkdir -p logs

# ── helper: create a lean file with minimal header ───────────────────────────

mk() {
  local path="$1"
  local title="$2"
  local ref="$3"

  cat > "$path" << EOF
/-!
# ${title}

## References
* ${ref}
-/
EOF
}

# ── Layer 1 — Allegory & Relator ─────────────────────────────────────────────

mk "CategoryTheory/Allegory/Basic.lean" \
   "Allegory" \
   "Freyd & Scedrov 1990"

mk "CategoryTheory/Allegory/Unitary.lean" \
   "Unitary Allegory" \
   "Freyd & Scedrov 1990"

mk "CategoryTheory/Allegory/LocallyComplete.lean" \
   "Locally Complete Allegory (Relation Algebra / RA)" \
   "Freyd & Scedrov 1990 / Def. 3.3"

mk "CategoryTheory/Allegory/Relator/Basic.lean" \
   "Relator, ColaxRelator, Semirelator, ωCocontinuousRelator" \
   "Kawahara 1973 / Bird & de Moor 1997 / Backhouse et al. 1991 / Backhouse & Hoogendijk 1993"

mk "CategoryTheory/Allegory/Relator/Cocartesian.lean" \
   "Cocartesian Decomposition and Cocartesian Relator Triple" \
   "Paper 2023"

# ── Layer 2 — TRA ────────────────────────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Basic.lean" \
   "Term Relation Algebra (TRA)" \
   "Paper 2023 / Paper 2026"

# ── Layer 3 — Expressiveness ─────────────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Properties.lean" \
   "Compatible, CUI, Substitutive, Leibniz's Law" \
   "Paper 2023 / Lassen 1998"

mk "CategoryTheory/Allegory/TRA/Modalities.lean" \
   "Modalities □, ♦ and Open Extension ♢" \
   "Lawvere 2007 / Kavvos 2019 / Lassen 1998"

mk "CategoryTheory/Allegory/TRA/FixedPointLemmas.lean" \
   "Lemma 16: Closed Monotone Functions Preserve Closedness Under Fixed Points" \
   "Paper 2026"

mk "CategoryTheory/Allegory/TRA/Harmony.lean" \
   "Harmony Axiom" \
   "Dummett 1991 / Prawitz 1965 / Harper 2016"

# ── Layer 4 — Operational Semantics ──────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Operational/Decomposition.lean" \
   "Operational Decomposition" \
   "Paper 2026"

mk "CategoryTheory/Allegory/TRA/Operational/GIP.lean" \
   "Gentzen's Inversion Principle (GIP)" \
   "Gentzen 1935 / Martin-Löf 1982"

mk "CategoryTheory/Allegory/TRA/Operational/GCP.lean" \
   "Gentzen's Conservation Principle (GCP)" \
   "Paper 2026"

mk "CategoryTheory/Allegory/TRA/Operational/FOperator.lean" \
   "aF Operator (Structural Recursion on Elimination Forms)" \
   "Paper 2026"

# ── Layer 5 — Reduction ───────────────────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Reduction/Basic.lean" \
   "Reduction" \
   "Bezem et al. 2003 — Term Rewriting Systems"

mk "CategoryTheory/Allegory/TRA/Reduction/Parallel.lean" \
   "Parallel Reduction a⇛ and Convertibility a≈" \
   "Takahashi 1995 / Howe 1996"

mk "CategoryTheory/Allegory/TRA/Reduction/Orthogonality.lean" \
   "Orthogonality Condition" \
   "Paper 2023"

mk "CategoryTheory/Allegory/TRA/Reduction/Confluence.lean" \
   "Church-Rosser Property, Diamond Property, Confluence, Theorem 21" \
   "Church & Rosser 1936 / Paper 2023, Thm. 21"

# ── Layer 6 — Evaluation ─────────────────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Evaluation/BigStep.lean" \
   "One-Step Evaluation aE, Big-Step Evaluation a⇓, Proposition 29" \
   "Kahn 1987 / Martin-Löf 1982, Prop. 29"

mk "CategoryTheory/Allegory/TRA/Evaluation/Determinism.lean" \
   "Theorem 31: Determinism of Big-Step Evaluation" \
   "Paper 2026"

# ── Layer 7 — Similarity & Congruence ────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Similarity/Basic.lean" \
   "b-Simulation, Similarity b⪆, Bisimilarity b=∼" \
   "Abramsky 1990 / Howe 1996, Sec. 6.1"

mk "CategoryTheory/Allegory/TRA/Similarity/HoweExtension.lean" \
   "Op-Howe Extension a§" \
   "Howe 1996 / Lassen 1998"

mk "CategoryTheory/Allegory/TRA/Similarity/Congruence.lean" \
   "Lemma 34 (Key Lemma) and Theorem 35: Congruence of Open Similarity" \
   "Paper 2026, Thm. 35 (NEW)"

# ── Layer 8 — Bridge Theorem ──────────────────────────────────────────────────

mk "CategoryTheory/Allegory/TRA/Bridge.lean" \
   "Lemma 36 and Theorem 37: Bridge Theorem (Main Result)" \
   "Paper 2026, Thm. 37 (NEW)"

# ── Layer 9 — Instances ───────────────────────────────────────────────────────

mk "Instances/FirstOrder/TRA.lean" \
   "First-Order Terms as TRA" \
   "Goguen et al. 1977 / Fiore, Plotkin & Turi 1999, Sec. 3.1.1"

mk "Instances/Lambda/Terms.lean" \
   "Lambda Calculus (Second-Order Terms) as TRA" \
   "Fiore, Plotkin & Turi 1999 / Aczel 1978-12, Sec. 3.1.2"

mk "Instances/Lambda/Operational.lean" \
   "Operational Decomposition for λ-Calculus" \
   "Paper 2026"

mk "Instances/Lambda/Beta.lean" \
   "β-Reduction: Reduction (I4), Determinism (I5), GCP (I6)" \
   "Paper 2026 — Example 19, Sec. 6.1.1"

mk "Instances/Lambda/Confluence.lean" \
   "Corollary: Bridge Theorem Instantiated on λ-Calculus (Church-Rosser, Determinism, Congruence)" \
   "Paper 2026 instantiated (I7, FINAL RESULT)"

echo "scaffold complete"
find CategoryTheory Instances logs -name '*.lean' | sort
