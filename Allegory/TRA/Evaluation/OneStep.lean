import Allegory.TRA.Operational.FOperator
import Allegory.TRA.Operational.GIP
import Allegory.TRA.Reduction.Basic
import Allegory.TRA.FixedPointLemmas

/-!
# B1 — One-Step Evaluation `aᴱ`

Defines one-step evaluation `aᴱ ≜ (a ∨ Δ)ᶠ` (Gavazzo, LICS 2026, Definition 27)
as the F-operator applied to the reflexive closure of `a`. Either relates
introduction forms with themselves or recursively evaluates major arguments of
an elimination form and then `a`-reduces. The closedness law `□aᴱ = (□a)ᴱ`
follows from Lemma 16 (E3) and is consumed by B2 (big-step evaluation) in
`Allegory/TRA/Evaluation/BigStep.lean`.

## Main definitions

* `Allegory.TRA.oneStep` — `aᴱ ≜ (a ∨ Δ)ᶠ`

## Main results

* `Allegory.TRA.oneStep_fixed_point` — fixed-point equation `aᴱ = (Δ ∨ ⟨aᴱ⟩) ; (a ∨ Δ)`
* `Allegory.TRA.box_oneStep_eq` — closure compatibility `□aᴱ = (□a)ᴱ`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 27
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **B1 — One-step evaluation** `aᴱ` (Paper 2026, Def. 27):
`aᴱ ≜ (a ∨ Δ)ᶠ`, the F-operator applied to the reflexive closure of `a`. -/
def oneStep {X : A} (a : X ⟶ X) : X ⟶ X :=
  fOperator (a ⊔ 𝟙 X)

/-- **Fixed-point equation for `aᴱ`** (Paper 2026, Def. 27):
`aᴱ = (Δ ∨ ⟨aᴱ⟩) ; (a ∨ Δ)`. Direct instance of `fOperator_fixed_point`. -/
theorem oneStep_fixed_point {X : A} (a : X ⟶ X) :
    oneStep a = (𝟙 X ⊔ bracketSingle (oneStep a)) ≫ (a ⊔ 𝟙 X) := by
  -- deps: fOperator_fixed_point
  sorry

/-- **`□aᴱ = (□a)ᴱ`** (Paper 2026, p. 76:21): the closure modality
distributes over one-step evaluation. Direct application of Lemma 16
to the closed function `fOperatorMap (a ⊔ Δ)`. -/
theorem box_oneStep_eq {X : A} (a : X ⟶ X) :
    box (oneStep a) = oneStep (box a) := by
  -- deps: box_lfp_eq_lfp_box, ClosedFn, boxOf, box_bracketRel_distrib, box_composition, box_monotonicity
  sorry

end Allegory.TRA
