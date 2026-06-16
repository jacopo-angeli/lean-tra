import Allegory.TRA.Evaluation.BigStep

/-!
# B3 — Proposition 29: Inductive Characterisation of `a⇓`

`a⇓` is the least solution of `x = Δ ∨ ⟨x⟩ ; a ; x` (Gavazzo, LICS 2026,
Proposition 29). For closed `a` this specialises to `x = Δκ ∨ ⟨x⟩ ; a ; x`. The
inductive characterisation is what makes the determinism argument in B4 work by
exposing `a⇓` as a least fixed point amenable to Knaster–Tarski induction.

## Main definitions

* `Allegory.TRA.bigStepInductiveMap` — monotone endofunction `x ↦ Δ ∨ ⟨x⟩ ; a ; x`
* `Allegory.TRA.bigStepInductiveMapClosed` — closed-case variant `x ↦ Δκ ∨ ⟨x⟩ ; a ; x`

## Main results

* `Allegory.TRA.bigStep_eq_lfp` — `a⇓ = lfp (bigStepInductiveMap a)`
* `Allegory.TRA.bigStep_eq_lfp_closed` — closed-case `a⇓ = lfp (bigStepInductiveMapClosed a)`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Proposition 29
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- The monotone endofunction `x ↦ Δ ∨ ⟨x⟩ ; a ; x` whose least fixed
point characterises `a⇓` (Paper 2026, Prop. 29). -/
def bigStepInductiveMap {X : A} (a : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := 𝟙 X ⊔ bracketSingle x ≫ a ≫ x
  monotone' := by
    -- deps: OperationalDecomposition.bracketRel_monotonicity_left, LocallyCompleteAllegory.comp_iSup_right, LocallyCompleteAllegory.iSup_comp_left, sup_le_sup_left
    sorry

/-- The closed-case monotone endofunction `x ↦ Δκ ∨ ⟨x⟩ ; a ; x`
(Paper 2026, Prop. 29, closed-`a` specialisation). -/
def bigStepInductiveMapClosed {X : A} (a : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := delta_kappa ⊔ bracketSingle x ≫ a ≫ x
  monotone' := by
    -- deps: bigStepInductiveMap.monotone'
    sorry

/-- **Proposition 29** (Paper 2026, p. 76:22): `a⇓` is the least fixed
point of `x ↦ Δ ∨ ⟨x⟩ ; a ; x`. -/
theorem bigStep_eq_lfp {X : A} (a : X ⟶ X) :
    bigStep a = OrderHom.lfp (bigStepInductiveMap a) := by
  -- deps: bigStep, kleeneStar_eval, oneStep, oneStep_fixed_point, fOperator_fixed_point, fOperator_least, OrderHom.map_lfp, OrderHom.lfp_le
  sorry

/-- **Proposition 29, closed case** (Paper 2026, p. 76:22): for closed
`a`, `a⇓` is the least fixed point of `x ↦ Δκ ∨ ⟨x⟩ ; a ; x`. -/
theorem bigStep_eq_lfp_closed {X : A} (a : X ⟶ X) (_h : Closed a) :
    bigStep a = OrderHom.lfp (bigStepInductiveMapClosed a) := by
  -- deps: bigStep_eq_lfp, closed_bigStep, delta_kappa_closed, closed_iff_eq_box, box_le_self, OrderHom.map_lfp, OrderHom.lfp_le
  sorry

end Allegory.TRA
