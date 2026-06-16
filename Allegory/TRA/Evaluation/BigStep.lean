import Allegory.TRA.Evaluation.OneStep

/-!
# B2 — Big-Step Evaluation `a⇓`

Iterates one-step evaluation until a canonical form: `a⇓ ≜ aᴱ* ; Δκ`
(Gavazzo, LICS 2026, Definition 28). The closure modality distributes over
big-step (`□a⇓ = (□a)⇓`) and closed reductions have closed big-step. These
laws feed Proposition 29 (B3) and the determinism theorem (B4) further down
the evaluation stack.

## Main definitions

* `Allegory.TRA.kleeneStarMap_eval` — local monotone endofunction `x ↦ Δ ∨ b ; x`
* `Allegory.TRA.kleeneStar_eval` — local Kleene star `b*`
* `Allegory.TRA.bigStep` — `a⇓ ≜ aᴱ* ; Δκ`

## Main results

* `Allegory.TRA.box_bigStep_eq` — `□a⇓ = (□a)⇓`
* `Allegory.TRA.closed_bigStep` — closed `a` ⟹ closed `a⇓`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 28
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- Local helper monotone map for Kleene star (`x ↦ Δ ∨ b ; x`). -/
def kleeneStarMap_eval {X : A} (b : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := 𝟙 X ⊔ b ≫ x
  monotone' := by
    -- deps: sup_le_sup_left, LocallyCompleteAllegory.comp_iSup_right
    sorry

/-- **Local Kleene star** `b*` (Paper 2026, A2 iteration). -/
def kleeneStar_eval {X : A} (b : X ⟶ X) : X ⟶ X :=
  OrderHom.lfp (kleeneStarMap_eval b)

/-- **B2 — Big-step evaluation** `a⇓` (Paper 2026, Def. 28):
`a⇓ ≜ aᴱ* ; Δκ`. -/
def bigStep {X : A} (a : X ⟶ X) : X ⟶ X :=
  kleeneStar_eval (oneStep a) ≫ delta_kappa

/-- **`□a⇓ = (□a)⇓`** (Paper 2026, p. 76:21): the closure modality
distributes over big-step evaluation. -/
theorem box_bigStep_eq {X : A} (a : X ⟶ X) :
    box (bigStep a) = bigStep (box a) := by
  -- deps: box_oneStep_eq, box_lfp_eq_lfp_box, ClosedFn, box_composition, delta_kappa_closed
  sorry

/-- **Closed ⟹ closed big-step** (Paper 2026, p. 76:21:
"If `a` closed then `a⇓` closed"): closure is preserved by `·⇓`. -/
theorem closed_bigStep {X : A} (a : X ⟶ X) (_h : Closed a) :
    Closed (bigStep a) := by
  -- deps: box_bigStep_eq, closed_iff_eq_box
  sorry

end Allegory.TRA
