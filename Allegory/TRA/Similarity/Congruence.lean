import Allegory.TRA.Similarity.HoweExtension
import Allegory.TRA.Operational.GCP
import Allegory.TRA.Harmony

/-!
# S3 — Lemma 34: Key Lemma for Congruence

Lemma 34 (Gavazzo, LICS 2026, §6.1): if `a` is a closed reflexive transitive
b-simulation and `b` satisfies GCP, then the op-Howe extension of `a` is an
open b-simulation, `a§ ≤ ♢B(a§)`. The proof goes by fixed-point induction on
`b⪆` using Harmony, GCP, and the four §-properties of `a§` from
`Allegory/TRA/Similarity/HoweExtension.lean`. The intermediate steps are
exposed as `keyLemma_harmony_step`, `keyLemma_gcp_step`, and
`keyLemma_open_step`; the main statement is `keyLemma_congruence`.

## Main results

* `Allegory.TRA.keyLemma_harmony_step` — Harmony specialisation used inside Lemma 34
* `Allegory.TRA.keyLemma_gcp_step` — GCP specialisation used inside Lemma 34
* `Allegory.TRA.keyLemma_open_step` — open-step commutation `♢b ; a§ ≤ a§ ; ♢b`
* `Allegory.TRA.keyLemma_congruence` — Lemma 34 itself

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, §6.1
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A] [Harmony A]

/-- **Harmony step** (Lemma 34 proof, key application of Harmony H1):
for any compatible relation `c`, `⟨â,a⟩ ; c ≤ c ; a[c]` specialised to
the `opHowe` candidate. -/
theorem keyLemma_harmony_step {X : A} (a c : X ⟶ X) (_hCompat : Compatible c) :
    OperationalDecomposition.bracketRel (tilde a) a ≫ c
      ≤ c ≫ substitution a c := by
  -- deps: Harmony.harmony, Compatible, OperationalDecomposition.bracketRel, tilde
  sorry

/-- **GCP step** (Lemma 34 proof, key application of GCP O3): specialised
to `x := opHowe a` to push `b` past `⟨tilde (a§), a§⟩`. -/
theorem keyLemma_gcp_step {X : A} (a b : X ⟶ X)
    (_hGCP : GCP b) (_hCompat : Compatible (opHowe a)) :
    OperationalDecomposition.bracketRel (tilde (opHowe a)) (opHowe a) ≫ b
      ≤ b ≫ substitution (opHowe a) (opHowe a) := by
  -- deps: GCP, opHowe_compatible
  sorry

/-- **Open-step inequality** (Lemma 34 proof, intermediate calculation):
`♢b ; a§ ≤ a§ ; ♢b`, the commutation used in the fixed-point induction. -/
theorem keyLemma_open_step {X : A} (a b : X ⟶ X)
    (_hSim : BSimulation b a) (_hClosed : Closed a)
    (_hRefl : 𝟙 X ≤ a) (_hTrans : a ≫ a ≤ a) (_hGCP : GCP b) :
    openExt b ≫ opHowe a ≤ opHowe a ≫ openExt b := by
  -- deps: keyLemma_harmony_step, howe_fixed_point, opHowe_compatible,
  --   opHowe_quasi_transitive, BSimulation, simulationFunctional, openExt,
  --   box_le_self, closed_iff_eq_box
  sorry

/-- **Lemma 34 — Key Lemma for congruence**: if `a` is a closed reflexive
transitive b-simulation and `b` satisfies GCP, then the op-Howe extension
of `a` is an open b-simulation, `a§ ≤ ♢B(a§)`. -/
theorem keyLemma_congruence {X : A} (a b : X ⟶ X)
    (_hSim : BSimulation b a) (_hClosed : Closed a)
    (_hRefl : 𝟙 X ≤ a) (_hTrans : a ≫ a ≤ a) (_hGCP : GCP b) :
    opHowe a ≤ openExt (simulationFunctional b (opHowe a)) := by
  -- deps: keyLemma_open_step, keyLemma_harmony_step, keyLemma_gcp_step,
  --   opHowe_reflexive, opHowe_substitutive, opHowe_compatible,
  --   opHowe_quasi_transitive, leftResidual, simulationFunctional,
  --   BSimulation, openExt, closed_iff_eq_box
  sorry

end Allegory.TRA
