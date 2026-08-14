/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Confluence.Orthogonal
public import LeanTra.Metatheory.GentzenPrinciples

/-! Alternative route to the diamond property of parallel reduction, from
local conditions on the rule. -/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA LeanTra.Confluence

open LeanTra.Metatheory

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

/-! ## Predicates -/

/-- A relation is *substitutive at identity* when substituting the monoid
identity is bounded by the relation itself: `a[1] ≤ a`. -/
def IsSubstitutiveAtIdentity (a : α) : Prop := SRA.subst a 1 ≤ a

/-- A relation is *deterministic* when its converse-post-composition is
sub-identity: `aᵒ * a ≤ 1`. Distinct from `IsDeterministicReduction`, which
is the same condition on the base substitution instance `a[1]`. -/
def IsDeterministic (a : α) : Prop := aᵒ * a ≤ 1

/-- The *structural* condition on the pair `(a, b)`: strict compatible
refinements of `b` can be pushed past `a` at the cost of substituting `b`
into itself: `tilde b * a ≤ a * b[b]`. -/
def Struct (a b : α) : Prop := SRA.scr b * a ≤ a * SRA.subst b b

/-! ## Six lemmas -/

/-- N1: `a ≤ a[1]`. -/
theorem le_substOne (a : α) : a ≤ SRA.subst a 1 := by
  calc a = SRA.subst a SRA.varDiag := (SRA.subst_varDiag_right a).symm
    _ ≤ SRA.subst a 1 := SRA.subst_mono_right SRA.varDiag_le_one

/-- N2: for a substitutive-at-identity `a`, `a[1] = a`. -/
theorem substOne_eq_of_substitutive {a : α} (h : IsSubstitutiveAtIdentity a) :
    SRA.subst a 1 = a :=
  le_antisymm h (le_substOne a)

/-- N3: `tilde t * hat u = tilde t * tilde u`, because the `varDiag` summand
in `hat u` is annihilated on the left by `tilde t`. -/
theorem scr_mul_cr (t u : α) : SRA.scr t * SRA.cr u = SRA.scr t * SRA.scr u := by
  unfold SRA.cr
  rw [Quantale.mul_sup_distrib,
      le_antisymm (SRA.scr_mul_varDiag_le_bot t) bot_le, bot_sup_eq]

/-- N4: for a reduction `a`, `aᵒ * Δη = ⊥`. -/
theorem converse_mul_varDiag_eq_bot {a : α} (h : IsReduction a) :
    aᵒ * SRA.varDiag = (⊥ : α) := by
  have hL : SRA.varDiag * a = (⊥ : α) := h
  have := congrArg IsInvolutiveQuantale.converse hL
  rw [IsInvolutiveQuantale.mul_converse, SRA.varDiag_converse,
      IsInvolutiveQuantale.converse_bot] at this
  exact this

/-- N5: converse of `Struct a b`, `aᵒ * tilde (bᵒ) ≤ bᵒ[bᵒ] * aᵒ`. -/
theorem struct_dual {a b : α} (h : Struct a b) :
    aᵒ * SRA.scr (bᵒ) ≤ SRA.subst (bᵒ) (bᵒ) * aᵒ := by
  have hL : SRA.scr b * a ≤ a * SRA.subst b b := h
  have := IsInvolutiveQuantale.converse_le_converse hL
  rw [IsInvolutiveQuantale.mul_converse, IsInvolutiveQuantale.mul_converse,
      ← SRA.scr_converse, SRA.subst_converse] at this
  exact this

/-- N6: for a reduction `a`, `(a⇛)ᵒ[(a⇛)ᵒ] ≤ (a⇛)ᵒ`, the converse of
`parRed_subst_le`. -/
theorem opParRed_subst_le {a : α} (h : IsReduction a) :
    SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  have hL := parRed_subst_le h
  have := IsInvolutiveQuantale.converse_le_converse hL
  rw [SRA.subst_converse] at this
  exact this

/-! ## PART 1 — abbreviations `A = parRed a`, `S = (parRed a)ᵒ`, `B = A * S` -/

/-- P1: `tilde B = tilde A * tilde S`. -/
theorem scr_B (a : α) :
    SRA.scr (parRed a * (parRed a)ᵒ)
      = SRA.scr (parRed a) * SRA.scr ((parRed a)ᵒ) :=
  SRA.scr_mul _ _

/-- P2: `Bᵒ = B`. -/
theorem B_converse (a : α) :
    (parRed a * (parRed a)ᵒ)ᵒ = parRed a * (parRed a)ᵒ := by
  rw [IsInvolutiveQuantale.mul_converse, IsInvolutiveQuantale.converse_involutive]

/-- P3: `tilde B ≤ B`. -/
theorem scr_B_le (a : α) :
    SRA.scr (parRed a * (parRed a)ᵒ) ≤ parRed a * (parRed a)ᵒ := by
  rw [scr_B]
  refine mul_le_mul' ?_ ?_
  · calc SRA.scr (parRed a)
        ≤ SRA.cr (parRed a) := by unfold SRA.cr; exact le_sup_right
      _ ≤ parRed a := cr_parRed_le a
  · calc SRA.scr ((parRed a)ᵒ)
        ≤ SRA.cr ((parRed a)ᵒ) := by unfold SRA.cr; exact le_sup_right
      _ ≤ (parRed a)ᵒ := cr_parRed_converse_le a

/-- P4: `(aᵒ ⊔ 1) * hat S = S`. -/
theorem sup_mul_cr_opHowe {a : α} (h2 : IsSubstitutiveAtIdentity a) :
    (aᵒ ⊔ 1) * SRA.cr ((parRed a)ᵒ) = (parRed a)ᵒ := by
  have hnorm : ((1 : α) ⊔ SRA.subst aᵒ 1) = aᵒ ⊔ 1 := by
    rw [← subst_one_converse a, substOne_eq_of_substitutive h2]
    exact sup_comm 1 aᵒ
  rw [← hnorm]
  conv_rhs => rw [parRed_converse a, SRA.opHowe_fix]
  rw [← parRed_converse a]

/-! ## PART 2 — the author's (1.1) and (1.2) -/

/-- L11: `aᵒ * tilde B * a ≤ B`. -/
theorem converse_mul_scr_B_mul_le {a : α}
    (h1 : IsReduction a) (h3 : IsDeterministic a)
    (h4 : Struct a ((parRed a)ᵒ)) :
    aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) * a ≤ parRed a * (parRed a)ᵒ := by
  have hstruct : SRA.scr ((parRed a)ᵒ) * a
               ≤ a * SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := h4
  have hstruct_dual : aᵒ * SRA.scr (parRed a)
                    ≤ SRA.subst (parRed a) (parRed a) * aᵒ := by
    have hd := struct_dual h4
    rwa [IsInvolutiveQuantale.converse_involutive] at hd
  calc aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) * a
      = aᵒ * (SRA.scr (parRed a) * SRA.scr ((parRed a)ᵒ)) * a := by rw [scr_B]
    _ = aᵒ * SRA.scr (parRed a) * (SRA.scr ((parRed a)ᵒ) * a) := by
        simp only [mul_assoc]
    _ ≤ aᵒ * SRA.scr (parRed a) * (a * SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ)) :=
        mul_le_mul' le_rfl hstruct
    _ = aᵒ * SRA.scr (parRed a) * a * SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := by
        simp only [mul_assoc]
    _ ≤ SRA.subst (parRed a) (parRed a) * aᵒ * a *
          SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) :=
        mul_le_mul' (mul_le_mul' hstruct_dual le_rfl) le_rfl
    _ = SRA.subst (parRed a) (parRed a) * (aᵒ * a) *
          SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := by
        simp only [mul_assoc]
    _ ≤ SRA.subst (parRed a) (parRed a) * 1 *
          SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) :=
        mul_le_mul' (mul_le_mul' le_rfl h3) le_rfl
    _ = SRA.subst (parRed a) (parRed a) *
          SRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := by rw [mul_one]
    _ ≤ parRed a * (parRed a)ᵒ :=
        mul_le_mul' (parRed_subst_le h1) (opParRed_subst_le h1)

/-- L12: `aᵒ * tilde B ≤ B`. -/
theorem converse_mul_scr_B_le {a : α}
    (h1 : IsReduction a) (h2 : IsSubstitutiveAtIdentity a)
    (h4 : Struct a ((parRed a)ᵒ)) :
    aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) ≤ parRed a * (parRed a)ᵒ := by
  have hstruct_dual : aᵒ * SRA.scr (parRed a)
                    ≤ SRA.subst (parRed a) (parRed a) * aᵒ := by
    have hd := struct_dual h4
    rwa [IsInvolutiveQuantale.converse_involutive] at hd
  calc aᵒ * SRA.scr (parRed a * (parRed a)ᵒ)
      = aᵒ * (SRA.scr (parRed a) * SRA.scr ((parRed a)ᵒ)) := by rw [scr_B]
    _ = aᵒ * SRA.scr (parRed a) * SRA.scr ((parRed a)ᵒ) := by
        simp only [mul_assoc]
    _ ≤ SRA.subst (parRed a) (parRed a) * aᵒ * SRA.scr ((parRed a)ᵒ) :=
        mul_le_mul' hstruct_dual le_rfl
    _ ≤ parRed a * aᵒ * SRA.scr ((parRed a)ᵒ) :=
        mul_le_mul' (mul_le_mul' (parRed_subst_le h1) le_rfl) le_rfl
    _ = parRed a * (aᵒ * SRA.scr ((parRed a)ᵒ)) := by simp only [mul_assoc]
    _ ≤ parRed a * ((aᵒ ⊔ 1) * SRA.cr ((parRed a)ᵒ)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_sup_left ?_)
        unfold SRA.cr; exact le_sup_right
    _ = parRed a * (parRed a)ᵒ := by rw [sup_mul_cr_opHowe h2]

/-- L21: `tilde B * a ≤ B`, obtained from L12 by transposition through
`P2` and `SRA.scr_converse`. -/
theorem scr_B_mul_le {a : α}
    (h1 : IsReduction a) (h2 : IsSubstitutiveAtIdentity a)
    (h4 : Struct a ((parRed a)ᵒ)) :
    SRA.scr (parRed a * (parRed a)ᵒ) * a ≤ parRed a * (parRed a)ᵒ := by
  have hL12 := converse_mul_scr_B_le h1 h2 h4
  have hconv := IsInvolutiveQuantale.converse_le_converse hL12
  rw [IsInvolutiveQuantale.mul_converse, IsInvolutiveQuantale.converse_involutive,
      ← SRA.scr_converse, B_converse a] at hconv
  exact hconv

/-! ## Leaves -/

/-- First leaf of the diamond split: the `aᵒ` summand of `aᵒ ⊔ 1`. -/
theorem converse_mul_scr_mul_le {a : α}
    (h1 : IsReduction a) (h2 : IsSubstitutiveAtIdentity a)
    (h3 : IsDeterministic a) (h4 : Struct a ((parRed a)ᵒ)) :
    aᵒ * SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a
      ≤ parRed a * (parRed a)ᵒ := by
  set Y : α := parRed a ⇨ₗ (parRed a * (parRed a)ᵒ) with hY
  have counit : Y * parRed a ≤ parRed a * (parRed a)ᵒ :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hpar : parRed a = SRA.cr (parRed a) * (a ⊔ 1) := by
    have hf : parRed a = SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) := SRA.howe_fix _
    rw [substOne_eq_of_substitutive h2, sup_comm 1 a] at hf
    exact hf
  calc aᵒ * SRA.cr Y * parRed a
      = aᵒ * (SRA.varDiag ⊔ SRA.scr Y) * parRed a := by rfl
    _ = (aᵒ * SRA.varDiag ⊔ aᵒ * SRA.scr Y) * parRed a := by
        rw [Quantale.mul_sup_distrib]
    _ = aᵒ * SRA.varDiag * parRed a ⊔ aᵒ * SRA.scr Y * parRed a := by
        rw [Quantale.sup_mul_distrib]
    _ = ⊥ * parRed a ⊔ aᵒ * SRA.scr Y * parRed a := by
        rw [converse_mul_varDiag_eq_bot h1]
    _ = ⊥ ⊔ aᵒ * SRA.scr Y * parRed a := by rw [Quantale.bot_mul]
    _ = aᵒ * SRA.scr Y * parRed a := bot_sup_eq _
    _ = aᵒ * SRA.scr Y * (SRA.cr (parRed a) * (a ⊔ 1)) := by
        conv_lhs => rw [hpar]
    _ = aᵒ * (SRA.scr Y * SRA.cr (parRed a)) * (a ⊔ 1) := by
        simp only [mul_assoc]
    _ = aᵒ * (SRA.scr Y * SRA.scr (parRed a)) * (a ⊔ 1) := by rw [scr_mul_cr]
    _ = aᵒ * SRA.scr (Y * parRed a) * (a ⊔ 1) := by rw [← SRA.scr_mul]
    _ ≤ aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) * (a ⊔ 1) :=
        mul_le_mul' (mul_le_mul' le_rfl (SRA.scr_mono counit)) le_rfl
    _ = aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) * a
          ⊔ aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) * 1 := by
        rw [Quantale.mul_sup_distrib]
    _ = aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) * a
          ⊔ aᵒ * SRA.scr (parRed a * (parRed a)ᵒ) := by rw [mul_one]
    _ ≤ parRed a * (parRed a)ᵒ :=
        sup_le (converse_mul_scr_B_mul_le h1 h3 h4)
               (converse_mul_scr_B_le h1 h2 h4)

/-- Second leaf of the diamond split: the `1` summand of `aᵒ ⊔ 1`. -/
theorem converse_mul_scr_le {a : α}
    (h1 : IsReduction a) (h2 : IsSubstitutiveAtIdentity a)
    (h4 : Struct a ((parRed a)ᵒ)) :
    (1 : α) * SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a
      ≤ parRed a * (parRed a)ᵒ := by
  rw [one_mul]
  set Y : α := parRed a ⇨ₗ (parRed a * (parRed a)ᵒ) with hY
  have counit : Y * parRed a ≤ parRed a * (parRed a)ᵒ :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hpar : parRed a = SRA.cr (parRed a) * (a ⊔ 1) := by
    have hf : parRed a = SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) := SRA.howe_fix _
    rw [substOne_eq_of_substitutive h2, sup_comm 1 a] at hf
    exact hf
  have h1_le_parRed_converse : (1 : α) ≤ (parRed a)ᵒ := by
    rw [← IsInvolutiveQuantale.converse_one]
    exact IsInvolutiveQuantale.converse_le_converse (one_le_parRed a)
  have piece_varDiag : SRA.varDiag * parRed a ≤ parRed a * (parRed a)ᵒ := by
    calc SRA.varDiag * parRed a
        ≤ 1 * parRed a := mul_le_mul' SRA.varDiag_le_one le_rfl
      _ = parRed a := one_mul _
      _ = parRed a * 1 := (mul_one _).symm
      _ ≤ parRed a * (parRed a)ᵒ := mul_le_mul' le_rfl h1_le_parRed_converse
  have piece_scr : SRA.scr Y * parRed a ≤ parRed a * (parRed a)ᵒ := by
    calc SRA.scr Y * parRed a
        = SRA.scr Y * (SRA.cr (parRed a) * (a ⊔ 1)) := by
          conv_lhs => rw [hpar]
      _ = (SRA.scr Y * SRA.cr (parRed a)) * (a ⊔ 1) := by simp only [mul_assoc]
      _ = (SRA.scr Y * SRA.scr (parRed a)) * (a ⊔ 1) := by rw [scr_mul_cr]
      _ = SRA.scr (Y * parRed a) * (a ⊔ 1) := by rw [← SRA.scr_mul]
      _ ≤ SRA.scr (parRed a * (parRed a)ᵒ) * (a ⊔ 1) :=
          mul_le_mul' (SRA.scr_mono counit) le_rfl
      _ = SRA.scr (parRed a * (parRed a)ᵒ) * a
            ⊔ SRA.scr (parRed a * (parRed a)ᵒ) * 1 := by
          rw [Quantale.mul_sup_distrib]
      _ = SRA.scr (parRed a * (parRed a)ᵒ) * a
            ⊔ SRA.scr (parRed a * (parRed a)ᵒ) := by rw [mul_one]
      _ ≤ parRed a * (parRed a)ᵒ :=
          sup_le (scr_B_mul_le h1 h2 h4) (scr_B_le a)
  calc SRA.cr Y * parRed a
      = (SRA.varDiag ⊔ SRA.scr Y) * parRed a := by rfl
    _ = SRA.varDiag * parRed a ⊔ SRA.scr Y * parRed a := by
        rw [Quantale.sup_mul_distrib]
    _ ≤ parRed a * (parRed a)ᵒ := sup_le piece_varDiag piece_scr

/-! ## Diamond -/

/-- Diamond property of parallel reduction from local conditions on the
rule: `IsReduction`, `IsSubstitutiveAtIdentity`, `IsDeterministic`, and the
structural condition `Struct a ((parRed a)ᵒ)`. -/
theorem diamond_parRed_of_struct {a : α}
    (h1 : IsReduction a) (h2 : IsSubstitutiveAtIdentity a)
    (h3 : IsDeterministic a) (h4 : Struct a ((parRed a)ᵒ)) :
    Diamond (parRed a) := by
  change (parRed a)ᵒ * parRed a ≤ parRed a * (parRed a)ᵒ
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  rw [parRed_converse a]
  refine SRA.opHowe_le_of_mul_cr_le ?_
  rw [← parRed_converse a]
  have h2' : (SRA.subst aᵒ 1 : α) = aᵒ := by
    rw [← subst_one_converse a, substOne_eq_of_substitutive h2]
  rw [h2', sup_comm]
  refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
  rw [Quantale.sup_mul_distrib, Quantale.sup_mul_distrib]
  refine sup_le ?_ ?_
  · exact converse_mul_scr_mul_le h1 h2 h3 h4
  · exact converse_mul_scr_le h1 h2 h4

end LeanTra.Confluence

#print axioms LeanTra.Confluence.le_substOne
#print axioms LeanTra.Confluence.substOne_eq_of_substitutive
#print axioms LeanTra.Confluence.scr_mul_cr
#print axioms LeanTra.Confluence.converse_mul_varDiag_eq_bot
#print axioms LeanTra.Confluence.struct_dual
#print axioms LeanTra.Confluence.opParRed_subst_le
#print axioms LeanTra.Confluence.scr_B
#print axioms LeanTra.Confluence.B_converse
#print axioms LeanTra.Confluence.scr_B_le
#print axioms LeanTra.Confluence.sup_mul_cr_opHowe
#print axioms LeanTra.Confluence.converse_mul_scr_B_mul_le
#print axioms LeanTra.Confluence.converse_mul_scr_B_le
#print axioms LeanTra.Confluence.scr_B_mul_le
#print axioms LeanTra.Confluence.converse_mul_scr_mul_le
#print axioms LeanTra.Confluence.converse_mul_scr_le
#print axioms LeanTra.Confluence.diamond_parRed_of_struct
