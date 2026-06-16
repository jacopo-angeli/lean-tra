import Allegory.TRA.Operational.Decomposition
import Mathlib.Order.FixedPoints

/-!
# O4 — `aᶠ` Operator (Structural Recursion on Elimination Forms)

The F-operator `aᶠ` is the least solution of `x = (Δ ∨ ⟨x⟩) ; a`
(Gavazzo, LICS 2026, §5.1.2.1). It refines the Howe extension `aᴴ` by acting on
elimination forms only — recursively evaluating major arguments — instead of
on all terms. It is the building block used by B1 (one-step evaluation
`aᴱ = (a ∨ Δ)ᶠ` in `Allegory/TRA/Evaluation/OneStep.lean`) and by B3
(Proposition 29 in `Allegory/TRA/Evaluation/Proposition29.lean`).

## Main definitions

* `Allegory.TRA.fOperatorMap` — monotone endofunction `x ↦ (Δ ∨ ⟨x⟩) ; a`
* `Allegory.TRA.fOperator` — `aᶠ`, the least fixed point of `fOperatorMap a`

## Main results

* `Allegory.TRA.fOperator_fixed_point` — fixed-point equation `aᶠ = (Δ ∨ ⟨aᶠ⟩) ; a`
* `Allegory.TRA.fOperator_least` — Knaster–Tarski induction principle for `aᶠ`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, §5.1.2.1
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- The monotone endofunction `x ↦ (Δ ∨ ⟨x⟩) ; a` whose least fixed point
defines `aᶠ` (Paper 2026, Sec. 5.1.2.1). -/
def fOperatorMap {X : A} (a : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := (𝟙 X ⊔ bracketSingle x) ≫ a
  monotone' := by
    -- deps: OperationalDecomposition.bracketRel_monotonicity_left, sup_le_sup_left, LocallyCompleteAllegory.iSup_comp_left
    sorry

/-- **`aᶠ` — F-operator** (Paper 2026, Sec. 5.1.2.1): the least fixed
point of `x ↦ (Δ ∨ ⟨x⟩) ; a` on the complete lattice `X ⟶ X`. -/
def fOperator {X : A} (a : X ⟶ X) : X ⟶ X :=
  OrderHom.lfp (fOperatorMap a)

/-- **Fixed-point equation** (Paper 2026, Sec. 5.1.2.1):
`aᶠ = (Δ ∨ ⟨aᶠ⟩) ; a`. -/
theorem fOperator_fixed_point {X : A} (a : X ⟶ X) :
    fOperator a = (𝟙 X ⊔ bracketSingle (fOperator a)) ≫ a := by
  -- deps: OrderHom.map_lfp
  sorry

/-- **Least pre-fixed point principle** (Knaster-Tarski induction for `aᶠ`):
`(Δ ∨ ⟨x⟩) ; a ≤ x ⟹ aᶠ ≤ x`. -/
theorem fOperator_least {X : A} (a x : X ⟶ X)
    (_h : (𝟙 X ⊔ bracketSingle x) ≫ a ≤ x) :
    fOperator a ≤ x := by
  -- deps: OrderHom.lfp_le
  sorry

end Allegory.TRA
