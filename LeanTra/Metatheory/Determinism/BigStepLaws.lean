/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Evaluation
public import LeanTra.Metatheory.GentzenPrinciples

/-!
# Big-step evaluation laws

Lemma A.6 and Figures 7–8 of the draft: the basic laws of big-step
evaluation for closed reductions.  (F4) is `bigStep_le_of_closed` above;
(F6), (F10), and (F11) consume `valDiag_mul_self` from Part B and
therefore inherit its `sorry`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Lemma A.6, Figures 7 and 8.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale LeanTra.Confluence

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- Lemma A.6, first half: for a closed reduction,
`a⇓ = Δκ ⊔ a * a⇓ ⊔ maj a⇓ * a⇓`.

**Status.** With `GIP a` and closedness, the derivation would route
through `bigStep_fix` (open) and `bigStep_isClosed` (open, refuted), each
needing `introDiag ≤ box _` or `oneStep a ≤ bigStep a`. Both trace to the
same refuted strict half. -/
theorem bigStep_fix_closed {a : α} (hGIP : GIP a) (h : a = SRA.box a) :
    bigStep a = valDiag ⊔ a * bigStep a ⊔ maj (bigStep a) * bigStep a := by
  sorry

/-- Lemma A.6, second half: for a closed reduction, if
`Δκ ⊔ a * x ⊔ maj x * x ≤ x` then `a⇓ ≤ x`.

**Status.** With `GIP a` and closedness, `bigStep_le_of_starNormalForm`
still needs `introDiag ≤ x`, but the hypothesis only supplies `valDiag ≤
x`; the missing step `introDiag ≤ valDiag` is exactly the refuted strict
half. `maj x * a ≤ x` (needed for `oneStep a ≤ x`) is not derivable from
`maj x * x ≤ x` without `1 ≤ x`. -/
theorem bigStep_le_of_closed {a x : α} (hGIP : GIP a) (h : a = SRA.box a)
    (hx : valDiag ⊔ a * x ⊔ maj x * x ≤ x) : bigStep a ≤ x := by
  sorry

/-! ### Figure 7 — basic laws of big-step evaluation -/

/-- Law (F1): `valDiag ≤ bigStep a`. -/
theorem F1 (a : α) : (valDiag : α) ≤ bigStep a := by
  have h_introDiag : (introDiag : α) ≤ bigStep a := by
    conv_rhs => rw [bigStep_fix_starNormalForm]
    exact le_sup_left
  exact (valDiag_le_introDiag).trans h_introDiag

/-- Law (F2): `a * bigStep a ≤ bigStep a`, under `GIP a`. -/
theorem F2 (a : α) (hGIP : GIP a) : a * bigStep a ≤ bigStep a := by
  -- Under GIP, `a ≤ oneStep a`: from `oneStep_fix hGIP`,
  -- `maj (oneStep a) * a ≤ oneStep a`, and `a ≤ maj introDiag * a ≤
  -- maj (oneStep a) * a` (since introDiag ≤ oneStep a).
  have hone_fix : oneStep a = introDiag ⊔ maj (oneStep a) * a := oneStep_fix hGIP
  have h_introDiag_le : (introDiag : α) ≤ oneStep a := by
    conv_rhs => rw [hone_fix]
    exact le_sup_left
  have h_maj_le : maj (introDiag : α) ≤ maj (oneStep a) :=
    elim_mono h_introDiag_le le_rfl
  have h_maj_a_le : maj (oneStep a) * a ≤ oneStep a := by
    conv_rhs => rw [hone_fix]
    exact le_sup_right
  have h_a_le_oneStep : a ≤ oneStep a := by
    calc a ≤ maj (introDiag : α) * a := hGIP
      _ ≤ maj (oneStep a) * a := mul_le_mul' h_maj_le le_rfl
      _ ≤ oneStep a := h_maj_a_le
  -- Then `a * bigStep a ≤ oneStep a * bigStep a ≤ bigStep a`.
  have h_onestep_big : oneStep a * bigStep a ≤ bigStep a := by
    conv_rhs => rw [bigStep_fix_starNormalForm a]
    exact le_sup_right
  calc a * bigStep a ≤ oneStep a * bigStep a :=
        mul_le_mul' h_a_le_oneStep le_rfl
    _ ≤ bigStep a := h_onestep_big

/-- Law (F3): `maj (bigStep a) * bigStep a ≤ bigStep a`, under `GIP a`.

**Status.** Reduces via `elim_mul_intro_le_bot` (killing `maj (bigStep a)
* introDiag`) and `bigStep_fix_starNormalForm` to `maj (bigStep a) *
oneStep a * bigStep a ≤ bigStep a`. Under GIP + `elim_mul` +
`introDiag_mul_oneStep hGIP`, this rewrites to `maj (bigStep a) * a *
bigStep a ≤ bigStep a`, which is exactly the elim-summand of `bigStep_fix`
(open). -/
theorem F3 (a : α) (hGIP : GIP a) :
    maj (bigStep a) * bigStep a ≤ bigStep a := by
  sorry

/-- Law (F4): `bigStep a ≤ x` whenever
`valDiag ⊔ a * x ⊔ maj x * x ≤ x`, for closed `a`. -/
theorem F4 (a x : α) (hGIP : GIP a) (hclosed : a = SRA.box a)
    (hx : valDiag ⊔ a * x ⊔ maj x * x ≤ x) : bigStep a ≤ x :=
  bigStep_le_of_closed hGIP hclosed hx

/-- Law (F5): `bigStep 1 ≤ 1`. -/
theorem F5 : bigStep (1 : α) ≤ 1 := by
  -- `oneStep 1 ≤ 1` via `evalRec_le_of` at `x = 1`:
  --   `(introDiag ⊔ maj 1) * (1 ⊔ introDiag) ≤ 1`.
  have h_one : oneStep (1 : α) ≤ 1 := by
    change evalRec ((1 : α) ⊔ introDiag) ≤ 1
    refine evalRec_le_of ?_
    have hIsup : ((1 : α) ⊔ introDiag) = 1 :=
      sup_of_le_left OperationalDecomposition.intro_one_le
    rw [hIsup, mul_one]
    refine sup_le OperationalDecomposition.intro_one_le ?_
    exact OperationalDecomposition.elim_one_one_le
  calc bigStep (1 : α)
      = (oneStep (1 : α))∗ * introDiag := rfl
    _ ≤ (1 : α)∗ * 1 := by
        exact mul_le_mul' (LeanTra.Confluence.star_mono h_one)
          OperationalDecomposition.intro_one_le
    _ = 1 := by rw [LeanTra.Confluence.star_one, mul_one]

/-- Law (F6): `bigStep a = bigStep a * valDiag`, under `GIP a`.

**Status.** Under GIP: the `≥` direction is easy (`bigStep a * valDiag ≤
bigStep a * introDiag = bigStep a`, using `valDiag ≤ introDiag` and
`introDiag * introDiag = introDiag`). The `≤` direction needs (F4) =
`bigStep_le_of_closed` and requires closedness of `a`, which the source
carries as a standing hypothesis. This signature omits closedness, so the
source's derivation cannot be reproduced. -/
theorem F6 (a : α) (hGIP : GIP a) : bigStep a = bigStep a * (valDiag : α) := by
  sorry

/-- Law (F7): `a ≤ b → bigStep a ≤ bigStep b`. -/
theorem F7 {a b : α} (h : a ≤ b) : bigStep a ≤ bigStep b := by
  have h_oneStep : oneStep a ≤ oneStep b := by
    change evalRec (a ⊔ introDiag) ≤ evalRec (b ⊔ introDiag)
    refine evalRec_le_of ?_
    have : ((introDiag : α) ⊔ maj (evalRec (b ⊔ introDiag))) * (a ⊔ introDiag)
         ≤ ((introDiag : α) ⊔ maj (evalRec (b ⊔ introDiag))) * (b ⊔ introDiag) :=
      mul_le_mul' le_rfl (sup_le_sup_right h _)
    exact this.trans (evalRec_fix _).ge
  calc bigStep a
      = (oneStep a)∗ * introDiag := rfl
    _ ≤ (oneStep b)∗ * introDiag :=
        mul_le_mul' (LeanTra.Confluence.star_mono h_oneStep) le_rfl
    _ = bigStep b := rfl

/-- Law (F8): `a ≤ SRA.box a → bigStep a ≤ SRA.box (bigStep a)`, under `GIP a`.

**Status.** Derived by the source from `box_bigStep` (Phase 1 item 4),
which is open. `bigStep_isClosed` (weak form) is also open with the same
refuted `introDiag ≤ box introDiag`. -/
theorem F8 {a : α} (hGIP : GIP a) (h : a ≤ SRA.box a) :
    bigStep a ≤ SRA.box (bigStep a) := by
  sorry

/-- Law (F9): if `valDiag ⊔ b * aᵒ ⊔ b * maj b ≤ b` then `(bigStep a)ᵒ ≤ b`,
under `GIP a`.

**Status.** Obtained by the source by dualising (F4). Since (F4) is open,
so is (F9). -/
theorem F9 {a b : α} (hGIP : GIP a)
    (h : (valDiag : α) ⊔ b * aᵒ ⊔ b * maj b ≤ b) : (bigStep a)ᵒ ≤ b := by
  sorry

/-- Law (F10): `valDiag * bigStep a = valDiag` when `a` is invertible.
`Inv a` implies `GIP a` via `gip_of_inv`, so no separate `hGIP` is needed.

**Status.** Source derivation routes through F4 (open). -/
theorem F10 (a : α) (hinv : Inv a) : (valDiag : α) * bigStep a = valDiag := by
  sorry

/-- Law (F11): `bigStep a * (bigStep a)ᵒ = bigStep a` when `a` is invertible.
`Inv a` implies `GIP a` via `gip_of_inv`, so no separate `hGIP` is needed.

**Status.** Source derivation chains F6, F10 (both open). -/
theorem F11 (a : α) (hinv : Inv a) : bigStep a * (bigStep a)ᵒ = bigStep a := by
  sorry

#print axioms OperationalDecomposition.bigStep_fix_closed
#print axioms OperationalDecomposition.bigStep_le_of_closed
#print axioms OperationalDecomposition.F1
#print axioms OperationalDecomposition.F2
#print axioms OperationalDecomposition.F3
#print axioms OperationalDecomposition.F4
#print axioms OperationalDecomposition.F5
#print axioms OperationalDecomposition.F6
#print axioms OperationalDecomposition.F7
#print axioms OperationalDecomposition.F8
#print axioms OperationalDecomposition.F9
#print axioms OperationalDecomposition.F10
#print axioms OperationalDecomposition.F11

end OperationalDecomposition
