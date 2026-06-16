import Allegory.TRA.Evaluation.Determinism
import Allegory.TRA.Similarity.Theorem35
import Allegory.TRA.Bridge.Lemma36
import Allegory.TRA.Reduction

/-!
# M2 — Theorem 37: Bridge Theorem (MAIN RESULT)

Theorem 37 (Gavazzo, LICS 2026, §6, main result): given a reduction `a` with
deterministic substitution instances, GIP, and GCP, all three metatheorems
bundle: (i) `a⇛` is confluent (R5 + M1), (ii) `(□a)⇓` is deterministic (B4),
(iii) `♢((□a)=∼)` is a congruence (S4). This unifies Aczel's confluence theorem
and Howe's congruence of bisimilarity in a single algebraic statement and is the
capstone of the TRA layer.

## Main results

* `Allegory.TRA.bridge_confluence` — Theorem 37 (i): confluence of `a⇛`
* `Allegory.TRA.bridge_determinism` — Theorem 37 (ii): determinism of `(□a)⇓`
* `Allegory.TRA.bridge_congruence` — Theorem 37 (iii): congruence of `♢((□a)=∼)`
* `Allegory.TRA.bridge_theorem` — bundled statement: confluence + determinism + congruence

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Theorem 37
* Aczel, P., *A general Church–Rosser theorem*, 1978
* Howe, D., *Proving congruence of bisimulation in functional programming languages*, 1996
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A] [Harmony A]

/-- **Bridge Theorem 37 (i)** — confluence (Paper 2026, p. 76:25):
`a[Δ]` deterministic + GIP + GCP ⟹ `a⇛` confluent. Via R5 + M1. -/
theorem bridge_confluence {X : A} (a : X ⟶ X) (_hRed : Reduction a) (_hDet : DeterministicSubstInstances a) (_hGIP : GIP a) (_hGCP : GCP a) :
    Confluent (parallelReduction a) := by
  -- deps: orthogonal_of_gip_gcp, orthogonal_imp_parallelReduction_confluent, Orthogonal, Confluent
  sorry

/-- **Bridge Theorem 37 (ii)** — determinism of big-step evaluation
(Paper 2026, p. 76:25): closed-reduction determinism is inherited by
`(□a)⇓`. Via B4. -/
theorem bridge_determinism {X : A} (a : X ⟶ X)
    (_hRed : Reduction a) (_hGIP : GIP a)
    (_hClosedDet : box a ≫ converse (box a) ≤ 𝟙 X) :
    converse (bigStep (box a)) ≫ bigStep (box a) ≤ delta_kappa := by
  -- deps: bigStep_deterministic, bigStep, box, closed_box, box_substitution_invariant, Reduction, GIP, delta_kappa
  sorry

/-- **Bridge Theorem 37 (iii)** — congruence of open bisimilarity
(Paper 2026, p. 76:25): GIP + GCP on the closed reduction lift to
congruence of `♢((□a)=∼)`. Via S4. -/
theorem bridge_congruence {X : A} (a : X ⟶ X)
    (_hRed : Reduction a) (_hGIP : GIP a) (_hGCP : GCP a) :
    Precongruence (openExt (sorry : X ⟶ X)) := by
  -- deps: openBisimilarity_congruence, bisimilarity, box, box_substitution_invariant, Precongruence
  sorry

/-- **Theorem 37 — Bridge Theorem** (Paper 2026, p. 76:25, MAIN RESULT):
the three metatheorems bundled. `a[Δ]` deterministic + GIP + GCP ⟹
confluence of parallel reduction, determinism of closed big-step
evaluation, and congruence of closed open bisimilarity. -/
theorem bridge_theorem {X : A} (a : X ⟶ X)
    (_hRed : Reduction a) (_hDet : DeterministicSubstInstances a)
    (_hGIP : GIP a) (_hGCP : GCP a)
    (_hClosedDet : box a ≫ converse (box a) ≤ 𝟙 X) :
    Confluent (parallelReduction a)
      ∧ converse (bigStep (box a)) ≫ bigStep (box a) ≤ delta_kappa
      ∧ Precongruence (openExt (sorry : X ⟶ X)) := by
  -- deps: bridge_confluence, bridge_determinism, bridge_congruence
  sorry

end Allegory.TRA
