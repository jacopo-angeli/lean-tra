/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Derived
public import LeanTra.Metatheory.Reduction
public import LeanTra.Metatheory.Confluence.Diamond
public import Mathlib.Order.FixedPoints

/-!
# Confluence of orthogonal reduction

Formalisation of the confluence-of-orthogonal-reduction theorem on top of
the abstract confluence layer in `Confluence/Diamond.lean`. Provides:
parallel reduction `parRed`, the orthogonality predicate `IsOrthogonal`,
the substitutivity result `parRed_subst_le`, and the two main theorems
`diamond_parRed` and `confluent_parRed`. Along the way develops the
op-Howe mirror `SRA.opHowe` and its converse identity `SRA.howe_converse`,
consumed only within this file.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Theorem 21.
* Francesco Gavazzo. *Allegories of Symbolic Manipulations.* LICS 2023,
  Theorem 6.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA LeanTra.Confluence

namespace SRA

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-! ### S-lemmas -/

/-- `1[1] = 1`: substituting the identity into the identity is the identity. -/
theorem subst_one_one : SRA.subst (1 : α) 1 = 1 := by
  refine le_antisymm ?_ ?_
  · refine subst_le_iff.mpr ?_
    refine one_le_of_cr_le ?_
    refine sup_le ?_ ?_
    · exact subst_le_iff.mp (by rw [SRA.subst_varDiag_left])
    · refine subst_le_iff.mp ?_
      calc SRA.subst (SRA.scr (SRA.substResid (1 : α) 1)) 1
          ≤ SRA.scr (SRA.subst (SRA.substResid (1 : α) 1) 1) := SRA.subst_scr_le _ _
        _ ≤ SRA.scr 1 := SRA.scr_mono (subst_le_iff.mpr le_rfl)
        _ ≤ 1 := scr_one_le
  · calc (1 : α)
        = SRA.subst SRA.varDiag 1 := (SRA.subst_varDiag_left 1).symm
      _ ≤ SRA.subst 1 1 := subst_mono_left varDiag_le_one

/-- `(hat a)[b] ≤ b ⊔ hat (a[b])`: substituting into a compatible refinement
is bounded by either returning `b` on the variable branch or refining the
substitution on the strict branch. -/
theorem cr_subst_le (a b : α) :
    SRA.subst (SRA.cr a) b ≤ b ⊔ SRA.cr (SRA.subst a b) := by
  unfold SRA.cr
  rw [subst_sup_left, SRA.subst_varDiag_left]
  exact sup_le_sup_left ((SRA.subst_scr_le _ _).trans le_sup_right) b

/-- Compatibility implies Leibniz: if `hat a ≤ a`, then `1[a] ≤ a`. -/
theorem subst_one_le_of_cr_le {a : α} (h : SRA.cr a ≤ a) :
    SRA.subst 1 a ≤ a := by
  refine subst_le_iff.mpr ?_
  refine one_le_of_cr_le ?_
  refine subst_le_iff.mp ?_
  calc SRA.subst (SRA.cr (SRA.substResid a a)) a
      ≤ a ⊔ SRA.cr (SRA.subst (SRA.substResid a a) a) := cr_subst_le _ _
    _ ≤ a ⊔ SRA.cr a := sup_le_sup_left (cr_mono (subst_le_iff.mpr le_rfl)) a
    _ ≤ a ⊔ a := sup_le_sup_left h a
    _ = a := sup_idem a

/-! ### Op-Howe extension `·§` -/

/-- Op-Howe recursor `x ↦ a * cr x`, bundled as an `OrderHom` so its least
fixed point can be taken via `OrderHom.lfp`. Mirror of `howeStep` with the
multiplication moved to the left. -/
def opHoweStep (a : α) : α →o α where
  toFun x := a * SRA.cr x
  monotone' _ _ h := mul_le_mul_right (cr_mono h) a

/-- Op-Howe extension `·§`: the unique solution of `x = a * cr x`, obtained
as the least fixed point of `opHoweStep`. Mirror of `howe`. -/
def opHowe (a : α) : α := (opHoweStep a).lfp

/-- Fixed-point law: `a§ = a * cr a§`. -/
theorem opHowe_fix (a : α) : opHowe a = a * SRA.cr (opHowe a) :=
  ((opHoweStep a).map_lfp).symm

/-- Fixed-point induction: `a§` is below every pre-fixed point of the
op-Howe recursor. -/
theorem opHowe_le_of_mul_cr_le ⦃a x : α⦄ (h : a * SRA.cr x ≤ x) :
    opHowe a ≤ x := (opHoweStep a).lfp_le h

/-- Any two solutions of `x = a * cr x` bound each other. -/
private theorem opHowe_solution_le {a b c : α}
    (hb : b = a * SRA.cr b) (hc : c = a * SRA.cr c) : b ≤ c := by
  rw [show b = b * 1 from (mul_one b).symm]
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine one_le_of_cr_le ?_
  refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
  calc b * SRA.cr (b ⇨ᵣ c)
      = (a * SRA.cr b) * SRA.cr (b ⇨ᵣ c) := by rw [← hb]
    _ = a * (SRA.cr b * SRA.cr (b ⇨ᵣ c)) := mul_assoc _ _ _
    _ = a * SRA.cr (b * (b ⇨ᵣ c)) := by rw [cr_mul]
    _ ≤ a * SRA.cr c := mul_le_mul_right
        (cr_mono (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl)) _
    _ = c := hc.symm

/-- Uniqueness of solutions of `x = a * cr x`. -/
theorem opHowe_unique {a b c : α} (hb : b = a * SRA.cr b)
    (hc : c = a * SRA.cr c) : b = c :=
  le_antisymm (opHowe_solution_le hb hc) (opHowe_solution_le hc hb)

/-- Anything satisfying the op-Howe equation equals `opHowe`. -/
theorem opHowe_eq_of_fix {a b : α} (hb : b = a * SRA.cr b) : b = opHowe a :=
  opHowe_unique hb (opHowe_fix a)

/-- Converse of Howe is op-Howe of converse: `(aᴴ)ᵒ = (aᵒ)§`. -/
theorem howe_converse (a : α) : (SRA.howe a)ᵒ = opHowe (aᵒ) := by
  refine opHowe_eq_of_fix ?_
  calc (SRA.howe a)ᵒ
      = (SRA.cr (SRA.howe a) * a)ᵒ := by rw [← howe_fix]
    _ = aᵒ * (SRA.cr (SRA.howe a))ᵒ := IsInvolutiveQuantale.mul_converse _ _
    _ = aᵒ * SRA.cr ((SRA.howe a)ᵒ) := by rw [cr_converse]

end SRA

/-! ## Confluence definitions -/

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-- Parallel reduction `a⇛`: the Howe extension of the reflexive
substitution closure `1 ⊔ a[1]` of `a`. Here `1` is the monoid unit (the
full identity), not `Δη` (the variable-restricted identity). -/
def parRed (a : α) : α := SRA.howe (1 ⊔ SRA.subst a 1)

/-! ### Elementary properties of `parRed` -/

/-- `1 ≤ 1 ⊔ a[1]`. -/
theorem one_le_parRed_arg (a : α) : (1 : α) ≤ 1 ⊔ SRA.subst a 1 :=
  le_sup_left

/-- Compatibility of parallel reduction: `hat (a⇛) ≤ a⇛`. -/
theorem cr_parRed_le (a : α) : SRA.cr (parRed a) ≤ parRed a := by
  unfold parRed
  calc SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1))
      = SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1)) * 1 := (mul_one _).symm
    _ ≤ SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1)) * (1 ⊔ SRA.subst a 1) :=
        mul_le_mul_right (one_le_parRed_arg a) _
    _ = SRA.howe (1 ⊔ SRA.subst a 1) := (SRA.howe_fix _).symm

/-- `1 ≤ a⇛`: the monoid identity sits below parallel reduction. -/
theorem one_le_parRed (a : α) : (1 : α) ≤ parRed a :=
  SRA.one_le_of_cr_le (cr_parRed_le a)

/-- Leibniz at `parRed`: `1[a⇛] ≤ a⇛`. -/
theorem subst_one_parRed_le (a : α) : SRA.subst 1 (parRed a) ≤ parRed a :=
  SRA.subst_one_le_of_cr_le (cr_parRed_le a)

/-! ### Substitutivity of `parRed` -/

/-- For a reduction `a`, the identity factors on the left as
`a = tilde 1 * a`. -/
theorem factor_scr_of_isReduction {a : α} (h : IsReduction a) :
    a = SRA.scr 1 * a := by
  have h' : SRA.varDiag * a = (⊥ : α) := h
  calc a
      = 1 * a := (one_mul _).symm
    _ = (SRA.varDiag ⊔ SRA.scr 1) * a := by
        rw [SRA.varDiag_sup_scr_one_eq]
    _ = SRA.varDiag * a ⊔ SRA.scr 1 * a := Quantale.sup_mul_distrib
    _ = ⊥ ⊔ SRA.scr 1 * a := by rw [h']
    _ = SRA.scr 1 * a := bot_sup_eq _

/-- For a reduction `a`, substituting the identity preserves reduction:
`Δη * a[1] = ⊥`. -/
theorem varDiag_mul_subst_one_eq_bot {a : α} (h : IsReduction a) :
    SRA.varDiag * SRA.subst a 1 = ⊥ := by
  refine le_antisymm ?_ bot_le
  have key : SRA.subst a 1 ≤ SRA.scr 1 * SRA.subst a 1 :=
    calc SRA.subst a 1
        = SRA.subst (SRA.scr 1 * a) (1 * 1) := by
            rw [← factor_scr_of_isReduction h, mul_one]
      _ ≤ SRA.subst (SRA.scr 1) 1 * SRA.subst a 1 := SRA.subst_mul_le _ _ _ _
      _ ≤ SRA.scr (SRA.subst 1 1) * SRA.subst a 1 :=
            mul_le_mul_left (SRA.subst_scr_le _ _) _
      _ = SRA.scr 1 * SRA.subst a 1 := by rw [SRA.subst_one_one]
  calc SRA.varDiag * SRA.subst a 1
      ≤ SRA.varDiag * (SRA.scr 1 * SRA.subst a 1) := mul_le_mul_right key _
    _ = SRA.varDiag * SRA.scr 1 * SRA.subst a 1 := (mul_assoc _ _ _).symm
    _ ≤ ⊥ * SRA.subst a 1 :=
          mul_le_mul_left (SRA.varDiag_mul_scr_le_bot _) _
    _ = ⊥ := Quantale.bot_mul

/-- Substitutivity of parallel reduction: for a reduction `a`,
`a⇛[a⇛] ≤ a⇛`. -/
theorem parRed_subst_le {a : α} (h : IsReduction a) :
    SRA.subst (parRed a) (parRed a) ≤ parRed a := by
  refine SRA.subst_le_iff.mpr ?_
  refine SRA.howe_le_of_cr_mul_le ?_
  refine SRA.subst_le_iff.mp ?_
  have hrw :
      SRA.cr (SRA.substResid (parRed a) (parRed a)) * (1 ⊔ SRA.subst a 1)
        = SRA.varDiag ⊔ SRA.scr (SRA.substResid (parRed a) (parRed a))
            ⊔ SRA.scr (SRA.substResid (parRed a) (parRed a)) * SRA.subst a 1 := by
    unfold SRA.cr
    rw [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
        Quantale.mul_sup_distrib, mul_one, mul_one,
        varDiag_mul_subst_one_eq_bot h, sup_bot_eq, ← sup_assoc]
  rw [hrw, SRA.subst_sup_left, SRA.subst_sup_left]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_of_eq (SRA.subst_varDiag_left _)
  · calc SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
        ≤ SRA.scr (SRA.subst (SRA.substResid (parRed a) (parRed a)) (parRed a)) :=
          SRA.subst_scr_le _ _
      _ ≤ SRA.scr (parRed a) := SRA.scr_mono (SRA.subst_le_iff.mpr le_rfl)
      _ ≤ SRA.cr (parRed a) := le_sup_right
      _ ≤ parRed a := cr_parRed_le a
  · calc SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a)) * SRA.subst a 1)
            (parRed a)
        = SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a)) * SRA.subst a 1)
            (parRed a * 1) := by rw [mul_one]
      _ ≤ SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
            * SRA.subst (SRA.subst a 1) 1 :=
            SRA.subst_mul_le _ _ _ _
      _ = SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
            * SRA.subst a 1 := by
            rw [SRA.subst_assoc, SRA.subst_one_one]
      _ ≤ SRA.cr (parRed a) * SRA.subst a 1 := by
          refine mul_le_mul_left ?_ _
          calc SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
              ≤ SRA.scr (SRA.subst (SRA.substResid (parRed a) (parRed a)) (parRed a)) :=
                SRA.subst_scr_le _ _
            _ ≤ SRA.scr (parRed a) :=
                SRA.scr_mono (SRA.subst_le_iff.mpr le_rfl)
            _ ≤ SRA.cr (parRed a) := le_sup_right
      _ ≤ SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
          mul_le_mul_right le_sup_right _
      _ = parRed a := (SRA.howe_fix _).symm

/-! ### Converse and nesting of `parRed` -/

/-- Converse of parallel reduction: `(a⇛)ᵒ = §(1 ⊔ aᵒ[1])`, the op-Howe
extension of the reflexive substitution closure of `aᵒ`. -/
theorem parRed_converse (a : α) :
    (parRed a)ᵒ = SRA.opHowe (1 ⊔ SRA.subst aᵒ 1) := by
  unfold parRed
  rw [SRA.howe_converse, IsInvolutiveQuantale.converse_sup,
      IsInvolutiveQuantale.converse_one, SRA.subst_converse,
      IsInvolutiveQuantale.converse_one]

/-- Nesting: `aᵒ[a⇛] ≤ a⇛ * aᵒ[1]`. -/
theorem nesting (a : α) :
    SRA.subst aᵒ (parRed a) ≤ parRed a * SRA.subst aᵒ 1 := by
  calc SRA.subst aᵒ (parRed a)
      = SRA.subst (1 * aᵒ) (parRed a * 1) := by rw [one_mul, mul_one]
    _ ≤ SRA.subst 1 (parRed a) * SRA.subst aᵒ 1 := SRA.subst_mul_le _ _ _ _
    _ ≤ parRed a * SRA.subst aᵒ 1 :=
        mul_le_mul_left (subst_one_parRed_le a) _

/-! ### Micro-lemmas for the diamond argument -/

/-- Converse commutes with base substitution: `(a[1])ᵒ = aᵒ[1]`. -/
theorem subst_one_converse (a : α) : (SRA.subst a 1)ᵒ = SRA.subst aᵒ 1 := by
  rw [SRA.subst_converse, IsInvolutiveQuantale.converse_one]

/-- Converse form of `varDiag_mul_subst_one_eq_bot`: for a reduction `a`,
`aᵒ[1] * Δη = ⊥`. -/
theorem subst_one_mul_varDiag_eq_bot {a : α} (h : IsReduction a) :
    SRA.subst aᵒ 1 * SRA.varDiag = (⊥ : α) := by
  have hL := varDiag_mul_subst_one_eq_bot h
  have := congrArg IsInvolutiveQuantale.converse hL
  rw [IsInvolutiveQuantale.mul_converse, subst_one_converse,
      SRA.varDiag_converse, IsInvolutiveQuantale.converse_bot] at this
  exact this

/-- Compatibility of the converse of parallel reduction: `hat ((a⇛)ᵒ) ≤ (a⇛)ᵒ`. -/
theorem cr_parRed_converse_le (a : α) : SRA.cr ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  rw [← SRA.cr_converse]
  exact IsInvolutiveQuantale.converse_le_converse (cr_parRed_le a)

/-- Leibniz at `(a⇛)ᵒ`: `1[(a⇛)ᵒ] ≤ (a⇛)ᵒ`. -/
theorem subst_one_parRed_converse_le (a : α) :
    SRA.subst 1 ((parRed a)ᵒ) ≤ (parRed a)ᵒ :=
  SRA.subst_one_le_of_cr_le (cr_parRed_converse_le a)

/-- Co-nesting: `a[(a⇛)ᵒ] ≤ a[1] * (a⇛)ᵒ`. -/
theorem co_nesting (a : α) :
    SRA.subst a ((parRed a)ᵒ) ≤ SRA.subst a 1 * (parRed a)ᵒ := by
  calc SRA.subst a ((parRed a)ᵒ)
      = SRA.subst (a * 1) (1 * (parRed a)ᵒ) := by rw [mul_one, one_mul]
    _ ≤ SRA.subst a 1 * SRA.subst 1 ((parRed a)ᵒ) := SRA.subst_mul_le _ _ _ _
    _ ≤ SRA.subst a 1 * (parRed a)ᵒ :=
        mul_le_mul_right (subst_one_parRed_converse_le a) _

/-- `hat (a⇛) * a[1] ≤ a⇛`. -/
theorem cr_mul_subst_le_parRed (a : α) :
    SRA.cr (parRed a) * SRA.subst a 1 ≤ parRed a :=
  calc SRA.cr (parRed a) * SRA.subst a 1
      ≤ SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
        mul_le_mul_right le_sup_right _
    _ = parRed a := (SRA.howe_fix _).symm

/-- Converse of `cr_mul_subst_le_parRed`: `aᵒ[1] * hat ((a⇛)ᵒ) ≤ (a⇛)ᵒ`. -/
theorem subst_one_mul_cr_parRed_converse_le (a : α) :
    SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  have hM6 := cr_mul_subst_le_parRed a
  have := IsInvolutiveQuantale.converse_le_converse hM6
  rw [IsInvolutiveQuantale.mul_converse, subst_one_converse,
      SRA.cr_converse] at this
  exact this

/-- `a` is *orthogonal* when its base substitution instances collapse on
overlaps: `(a[1])ᵒ * a[1] ≤ 1` (two `a`-rewrites of the same term differ
only by variable renaming) and `(a[1])ᵒ * tilde (a⇛) ≤ aᵒ[a⇛]` (a
base-instance backwards step followed by a strict compatible refinement of
parallel reduction can be swapped for a substituted converse). -/
def IsOrthogonal (a : α) : Prop :=
  (SRA.subst a 1)ᵒ * SRA.subst a 1 ≤ 1
    ∧ (SRA.subst a 1)ᵒ * SRA.scr (parRed a) ≤ SRA.subst aᵒ (parRed a)

/-! ### Diamond and confluence -/

/-- Converse form of the second orthogonality conjunct:
`tilde ((a⇛)ᵒ) * a[1] ≤ a[(a⇛)ᵒ]`. -/
theorem scr_parRed_converse_mul_le {a : α} (horth : IsOrthogonal a) :
    SRA.scr ((parRed a)ᵒ) * SRA.subst a 1 ≤ SRA.subst a ((parRed a)ᵒ) := by
  have h2 := horth.2
  have := IsInvolutiveQuantale.converse_le_converse h2
  rw [IsInvolutiveQuantale.mul_converse, IsInvolutiveQuantale.converse_involutive,
      SRA.subst_converse, IsInvolutiveQuantale.converse_involutive,
      ← SRA.scr_converse] at this
  exact this

/-- Diamond property of parallel reduction: for a reduction `a` satisfying
orthogonality, `(a⇛)ᵒ * a⇛ ≤ a⇛ * (a⇛)ᵒ`. -/
theorem diamond_parRed {a : α} (h : IsReduction a) (horth : IsOrthogonal a) :
    Diamond (parRed a) := by
  change (parRed a)ᵒ * parRed a ≤ parRed a * (parRed a)ᵒ
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  rw [parRed_converse a]
  refine SRA.opHowe_le_of_mul_cr_le ?_
  rw [← parRed_converse a]
  refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
  have hU : (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a
              ≤ parRed a * (parRed a)ᵒ :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hmid :
      SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a)
        ≤ SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) := by
    calc SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a)
        = SRA.cr ((parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a) :=
            SRA.cr_mul _ _
      _ ≤ SRA.cr (parRed a * (parRed a)ᵒ) := SRA.cr_mono hU
      _ = SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) := (SRA.cr_mul _ _).symm
  have Hleft :
      SRA.subst aᵒ 1 * SRA.cr (parRed a) ≤ parRed a * SRA.subst aᵒ 1 := by
    unfold SRA.cr
    rw [Quantale.mul_sup_distrib]
    refine sup_le ?_ ?_
    · calc SRA.subst aᵒ 1 * SRA.varDiag
          = (⊥ : α) := subst_one_mul_varDiag_eq_bot h
        _ ≤ parRed a * SRA.subst aᵒ 1 := bot_le
    · have h2 := horth.2
      rw [subst_one_converse] at h2
      exact h2.trans (nesting a)
  have Hright :
      SRA.cr ((parRed a)ᵒ) * SRA.subst a 1
        ≤ SRA.subst a 1 * (parRed a)ᵒ := by
    unfold SRA.cr
    rw [Quantale.sup_mul_distrib]
    refine sup_le ?_ ?_
    · calc SRA.varDiag * SRA.subst a 1
          = (⊥ : α) := varDiag_mul_subst_one_eq_bot h
        _ ≤ SRA.subst a 1 * (parRed a)ᵒ := bot_le
    · exact (scr_parRed_converse_mul_le horth).trans (co_nesting a)
  have Hdet : SRA.subst aᵒ 1 * SRA.subst a 1 ≤ (1 : α) := by
    have h1 := horth.1
    rw [subst_one_converse] at h1
    exact h1
  have hfix : parRed a = SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
    SRA.howe_fix _
  nth_rewrite 4 [hfix]
  rw [show ∀ A B C D : α, A * B * (C * D) = A * (B * C) * D from
        fun _ _ _ _ => by simp only [mul_assoc]]
  calc (1 ⊔ SRA.subst aᵒ 1)
          * (SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a))
          * (1 ⊔ SRA.subst a 1)
      ≤ (1 ⊔ SRA.subst aᵒ 1)
          * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
          * (1 ⊔ SRA.subst a 1) :=
          mul_le_mul_left (mul_le_mul_right hmid _) _
    _ ≤ parRed a * (parRed a)ᵒ := ?_
  simp only [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
             one_mul, mul_one]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact mul_le_mul' (cr_parRed_le a) (cr_parRed_converse_le a)
  · calc SRA.subst aᵒ 1 * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
        = SRA.subst aᵒ 1 * SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) :=
            (mul_assoc _ _ _).symm
      _ ≤ parRed a * SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ) :=
            mul_le_mul_left Hleft _
      _ = parRed a * (SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ)) := mul_assoc _ _ _
      _ ≤ parRed a * (parRed a)ᵒ :=
            mul_le_mul_right (subst_one_mul_cr_parRed_converse_le a) _
  · calc SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) * SRA.subst a 1
        = SRA.cr (parRed a) * (SRA.cr ((parRed a)ᵒ) * SRA.subst a 1) :=
            mul_assoc _ _ _
      _ ≤ SRA.cr (parRed a) * (SRA.subst a 1 * (parRed a)ᵒ) :=
            mul_le_mul_right Hright _
      _ = SRA.cr (parRed a) * SRA.subst a 1 * (parRed a)ᵒ :=
            (mul_assoc _ _ _).symm
      _ ≤ parRed a * (parRed a)ᵒ :=
            mul_le_mul_left (cr_mul_subst_le_parRed a) _
  · calc SRA.subst aᵒ 1 * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
            * SRA.subst a 1
        = (SRA.subst aᵒ 1 * SRA.cr (parRed a))
            * (SRA.cr ((parRed a)ᵒ) * SRA.subst a 1) := by
            simp only [mul_assoc]
      _ ≤ (parRed a * SRA.subst aᵒ 1) * (SRA.subst a 1 * (parRed a)ᵒ) :=
            mul_le_mul' Hleft Hright
      _ = parRed a * (SRA.subst aᵒ 1 * SRA.subst a 1) * (parRed a)ᵒ := by
            simp only [mul_assoc]
      _ ≤ parRed a * 1 * (parRed a)ᵒ :=
            mul_le_mul_left (mul_le_mul_right Hdet _) _
      _ = parRed a * (parRed a)ᵒ := by rw [mul_one]

/-- Confluence of parallel reduction: for a reduction `a` satisfying
orthogonality, `Confluent (parRed a)`. -/
theorem confluent_parRed {a : α} (h : IsReduction a) (horth : IsOrthogonal a) :
    Confluent (parRed a) :=
  (diamond_parRed h horth).confluent

end LeanTra.Confluence

#print axioms SRA.subst_one_one
#print axioms SRA.subst_one_le_of_cr_le
#print axioms SRA.howe_converse
#print axioms LeanTra.Confluence.parRed_subst_le
#print axioms LeanTra.Confluence.diamond_parRed
#print axioms LeanTra.Confluence.confluent_parRed
