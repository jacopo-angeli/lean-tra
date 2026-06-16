import Allegory.TRA.Modalities
import Mathlib.Order.FixedPoints

/-!
# E3 — Lemma 16: Closed Monotone Functions Preserve Closedness Under Fixed Points

A closed monotone endofunction on a TRA preserves closure at the level of least
fixed points: if `F` is closed (`□F(x) ≤ F(□x)`) then `□(μF) = μ(λ x. □F(x))`,
and consequently `μF` is closed. This expresses a compatibility between the S4
modality `□` and Knaster–Tarski fixed point theory, showing that modal closure
is preserved under recursion. The result is Lemma 16 in Gavazzo (LICS 2026,
§3.2.1) and is reused throughout the operational layer — in particular by B1
(`box_oneStep_eq`) and B2 (`box_bigStep_eq`) to lift `□` past Kleene iterations.

## Main definitions

* `Allegory.TRA.ClosedFn` — predicate `∀ x, □F(x) ≤ F(□x)` characterising closed monotone endofunctions
* `Allegory.TRA.boxOf` — the monotone endofunction `x ↦ □F(x)`

## Main results

* `Allegory.TRA.box_lfp_eq_lfp_box` — Lemma 16: `□(μF) = μ(boxOf F)` for closed `F`
* `Allegory.TRA.closed_lfp` — Corollary: the least fixed point of a closed function is itself closed

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Lemma 16
-/

open CategoryTheory

  namespace Allegory.TRA

  variable {A : Type*} [TRA A]

  /-- A monotone endofunction `F` on `X ⟶ X` is **closed** when
  `□F(x) ≤ F(□x)` for every `x` (Paper 2026, Lemma 16 hypothesis). -/
  def ClosedFn {X : A} (F : (X ⟶ X) →o (X ⟶ X)) : Prop := ∀ x, box (F x) ≤ F (box x)

  /-- The composition `box ∘ F` as a monotone endofunction
  (Paper 2026, Lemma 16: the right-hand side of `μ(λ x. □F(x))`). -/
  def boxOf {X : A} (F : (X ⟶ X) →o (X ⟶ X)) : (X ⟶ X) →o (X ⟶ X) where
    toFun x := box (F x)
    monotone' := fun _ _ h => box_monotonicity (F.monotone' h)

  /-- **Lemma 16** (Paper 2026, p. 76:16): if `F` is closed then the box
  of its least fixed point equals the least fixed point of `box ∘ F`. -/
  theorem box_lfp_eq_lfp_box {X : A} (F : (X ⟶ X) →o (X ⟶ X)) (_hF : ClosedFn F) :
    box (OrderHom.lfp F) = OrderHom.lfp (boxOf F) := by
      -- deps: OrderHom.lfp, OrderHom.map_lfp, OrderHom.lfp_le, box_le_self, box_monotonicity, le_antisymm
      sorry

  /-- **Corollary of Lemma 16**: the least fixed point of a closed function
  is itself closed (Paper 2026, p. 76:16, used in Theorem 31). -/
  theorem closed_lfp {X : A} (F : (X ⟶ X) →o (X ⟶ X)) (_hF : ClosedFn F) :
    Closed (OrderHom.lfp F) := by
      -- deps: OrderHom.map_lfp, OrderHom.lfp_le, box_le_self, box_lfp_eq_lfp_box
      sorry

end Allegory.TRA
