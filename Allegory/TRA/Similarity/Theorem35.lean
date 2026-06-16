import Allegory.TRA.Similarity.Congruence
import Allegory.TRA.Similarity.HoweExtension
import Allegory.TRA.Evaluation.BigStep
import Allegory.TRA.Operational.GCP
import Allegory.TRA.Harmony

/-!
# S4 — Theorem 35: Congruence of Open Similarity

Theorem 35 (Gavazzo, LICS 2026, §6.1): `♢b⪆` is substitutive and compatible, and
`♢b=∼` is a congruence. This is the coinductive consequence of Lemma 34 (S3) and
the §-properties (S2), and supplies clause (iii) of the Bridge Theorem (M2) in
`Allegory/TRA/Bridge.lean`. The proof goes through the key equality
`b⪆§ = ♢b⪆` and then transfers compatibility and substitutivity from the op-Howe
extension via `Allegory/TRA/Similarity/HoweExtension.lean`.

## Main results

* `Allegory.TRA.opHowe_similarity_le_openSimilarity` — `b⪆§ ≤ ♢b⪆` (coinductive step)
* `Allegory.TRA.openSimilarity_le_opHowe_similarity` — `♢b⪆ ≤ b⪆§` (easy direction)
* `Allegory.TRA.opHowe_similarity_eq_openSimilarity` — key equality `b⪆§ = ♢b⪆`
* `Allegory.TRA.openSimilarity_compatible` — `♢b⪆` is compatible
* `Allegory.TRA.openSimilarity_substitutive` — `♢b⪆` is substitutive
* `Allegory.TRA.openBisimilarity_congruence` — Theorem 35: `♢b=∼` is a precongruence

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, §6.1
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A] [Harmony A]

/-- **`b⪆§ ≤ ♢b⪆`** (Paper 2026, Thm. 35 proof, coinductive step):
the op-Howe extension of similarity sits inside open similarity. -/
theorem opHowe_similarity_le_openSimilarity {X : A} (b : X ⟶ X)
    (_hGCP : GCP b) :
    opHowe (similarity b) ≤ openSimilarity b := by
  -- deps: keyLemma_congruence, similarity, similarityMap, openSimilarity, similarity_closed, similarity_transitive, OrderHom.le_gfp, OrderHom.gfp, opHowe, opHowe_reflexive
  sorry

/-- **`♢b⪆ ≤ b⪆§`** (Paper 2026, Thm. 35 proof, easy direction):
open similarity sits inside the op-Howe extension. -/
theorem openSimilarity_le_opHowe_similarity {X : A} (b : X ⟶ X) :
    openSimilarity b ≤ opHowe (similarity b) := by
  -- deps: openSimilarity, similarity_closed, similarity_transitive, opHowe, opHowe_quasi_transitive, opHowe_reflexive, openExt, box_le_self
  sorry

/-- **`b⪆§ = ♢b⪆`** (Paper 2026, Thm. 35 proof, key equality):
the two extensions coincide. -/
theorem opHowe_similarity_eq_openSimilarity {X : A} (b : X ⟶ X)
    (_hGCP : GCP b) :
    opHowe (similarity b) = openSimilarity b := by
  -- deps: opHowe_similarity_le_openSimilarity, openSimilarity_le_opHowe_similarity, le_antisymm
  sorry

/-- **`♢b⪆` is compatible** (Paper 2026, Thm. 35, part 1):
the open similarity is closed under term constructors. -/
theorem openSimilarity_compatible {X : A} (b : X ⟶ X) (_hGCP : GCP b) :
    Compatible (openSimilarity b) := by
  -- deps: opHowe_similarity_eq_openSimilarity, opHowe_compatible, Compatible
  sorry

/-- **`♢b⪆` is substitutive** (Paper 2026, Thm. 35, part 2):
the open similarity is closed under substitution. -/
theorem openSimilarity_substitutive {X : A} (b : X ⟶ X) (_hGCP : GCP b) :
    Substitutive (openSimilarity b) := by
  -- deps: opHowe_similarity_eq_openSimilarity, opHowe_substitutive, Substitutive, similarity_closed, similarity_transitive
  sorry

/-- **Theorem 35** (Paper 2026, p. 76:24) — **Congruence of open
similarity**: `♢b=∼` is a congruence (precongruence + symmetry). -/
theorem openBisimilarity_congruence {X : A} (b : X ⟶ X) (_hGCP : GCP b) :
    Precongruence (openExt (sorry : X ⟶ X)) := by
  -- deps: openSimilarity_compatible, openSimilarity_substitutive, bisimilarity, Precongruence, openExt, closed_iff_eq_box, box_le_self
  sorry

end Allegory.TRA
