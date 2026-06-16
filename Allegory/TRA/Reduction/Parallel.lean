import Allegory.TRA.Reduction.Basic
import Allegory.TRA.Properties
import Mathlib.Order.FixedPoints

/-!
# R2 — Parallel Reduction `a⇛` and Convertibility `a≈`

Defines Takahashi-style parallel reduction `a⇛ ≜ (Δ ∨ a[Δ])ᴴ` and convertibility
`a≈ ≜ (a⇛ ∨ a⇛°)*` inside a TRA (Gavazzo, LICS 2026, §4). Parallel reduction is
the Howe extension of the reflexive closure of substitution-instances of `a`,
and convertibility is the Kleene star of the symmetric closure of parallel
reduction. Both are central inputs to the confluence theorem in
`Allegory/TRA/Reduction.lean` (R5 / Theorem 21).

## Main definitions

* `Allegory.TRA.kleeneStarMap` — local monotone endofunction `x ↦ Δ ∨ b ; x`
* `Allegory.TRA.kleeneStar` — local Kleene star `b*`
* `Allegory.TRA.parallelReduction` — `a⇛ ≜ (Δ ∨ a[Δ])ᴴ`
* `Allegory.TRA.convertibility` — `a≈ ≜ (a⇛ ∨ a⇛°)*`

## Main results

* `Allegory.TRA.parallelReduction_fixed_point` — fixed-point equation for `a⇛`
* `Allegory.TRA.convertibility_eq_howe_star` — alternative characterisation `a≈ = (a ∨ a°)ᴴ*`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, §4
* Takahashi, M., *Parallel reductions in λ-calculus*, 1995
* Howe, D., *Proving congruence of bisimulation in functional programming languages*, 1996
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A]

/-- The monotone endofunction `x ↦ Δ ∨ b ; x` whose least fixed point is
the Kleene star `b*`. Local helper because Kleene star is not yet exposed
in `Allegory/LocallyComplete.lean`. -/
def kleeneStarMap {X : A} (b : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := 𝟙 X ⊔ b ≫ x
  monotone' := by
    -- deps: sup_le_sup_left, LocallyCompleteAllegory.comp_iSup_right
    sorry

/-- **Kleene star** `b*` (Paper 2026, derived from A2: `a* = μx. Δ ∨ a;x`).
Local definition; should eventually live in `Allegory/LocallyComplete.lean`. -/
def kleeneStar {X : A} (b : X ⟶ X) : X ⟶ X :=
  OrderHom.lfp (kleeneStarMap b)

/-- **Parallel reduction** `a⇛ ≜ (Δ ∨ a[Δ])ᴴ` (Paper 2026, Sec. 4):
Howe extension of the reflexive closure of substitution-instances of `a`. -/
def parallelReduction {X : A} (a : X ⟶ X) : X ⟶ X :=
  howe (𝟙 X ⊔ substitution a (𝟙 X))

/-- **Convertibility** `a≈ ≜ (a⇛ ∨ a⇛°)*` (Paper 2026, Sec. 4): Kleene
star of the symmetric closure of parallel reduction. -/
def convertibility {X : A} (a : X ⟶ X) : X ⟶ X :=
  kleeneStar (parallelReduction a ⊔ converse (parallelReduction a))

/-- **Fixed-point equation for parallel reduction** (Paper 2026, Sec. 4):
`a⇛ = (Δ ∨ ⟨a⇛⟩ ∨ a[Δ]) ; (Δ ∨ a[Δ])` — direct instance of
`howe_fixed_point` at `(Δ ∨ a[Δ])`. -/
theorem parallelReduction_fixed_point {X : A} (a : X ⟶ X) :
    parallelReduction a
      = (delta_eta ⊔ tilde (parallelReduction a)) ≫ (𝟙 X ⊔ substitution a (𝟙 X)) := by
  -- deps: howe_fixed_point
  sorry

/-- **Alternative characterisation of convertibility**:
`a≈ = (a ∨ a°)ᴴ*` (Paper 2026, Sec. 4, line 705-706: "Standard
algebraic TRA calculations show that `a≈ ≜ (a⇛ ∨ a⇛°)*`"). -/
theorem convertibility_eq_howe_star {X : A} (a : X ⟶ X) :
    convertibility a = kleeneStar (howe (a ⊔ converse a)) := by
  -- deps: howe, howe_uniqueness, tilde_converse, converse, ⊔
  sorry

end Allegory.TRA
