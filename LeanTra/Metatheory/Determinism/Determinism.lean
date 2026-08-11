/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Determinism.BigStepLaws

/-!
# Determinism

The determinism hypothesis, the inversion lemma (Proposition A.9),
Lemma A.11, and Theorem A.12 (determinism of big-step evaluation for
closed, invertible reductions).

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Proposition A.9, Lemma A.11, Theorem A.12 (and Theorem 5.9).
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

open LeanTra.Confluence

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- A reduction `a` is deterministic when `aᵒ * a ≤ 1`: the two ends of a
rewrite of the same term agree up to renaming. This is the paper's first
orthogonality condition (Theorem 5.9 / Theorem A.12). -/
def IsDeterministicRule (a : α) : Prop := aᵒ * a ≤ 1

/-- Proposition A.9 (Inversion Lemma): for a closed, invertible reduction `a`,
the major-slot projection of any `b` composed with `bigStep a` factors through
`bigStep` of the major-slot projection of `b` times `bigStep a`.

The derivation unfolds `bigStep a` with the closed fixed-point law
`bigStep_fix_of_closed`, distributes `maj b` over the resulting join, kills the
`maj b * valDiag` summand through `maj_mul_introDiag_le_bot`, then rewrites
`maj b * maj (bigStep a)` to `maj (b * bigStep a)` via `elim_mul`; (F2) finally
absorbs the trailing `a * bigStep a`. Hypothesis `hinv` is inherited from the
paper's Remark A.8 (Section A.1 background) but is not needed by the algebra. -/
theorem maj_mul_bigStep_le {a : α} (hclosed : a = SRA.box a) (_hinv : Inv a)
    (b : α) : maj b * bigStep a ≤ maj (b * bigStep a) * bigStep a := by
  have hfix : bigStep a = valDiag ⊔ maj (bigStep a) * a * bigStep a :=
    bigStep_fix_of_closed hclosed
  have h_elim_mul : maj b * maj (bigStep a) = maj (b * bigStep a) := by
    change OperationalDecomposition.elim b 1
             * OperationalDecomposition.elim (bigStep a) 1
         = OperationalDecomposition.elim (b * bigStep a) 1
    rw [← OperationalDecomposition.elim_mul, mul_one]
  calc maj b * bigStep a
      = maj b * (valDiag ⊔ maj (bigStep a) * a * bigStep a) := by rw [← hfix]
    _ = maj b * valDiag
          ⊔ maj b * (maj (bigStep a) * a * bigStep a) :=
        Quantale.mul_sup_distrib
    _ ≤ maj b * introDiag
          ⊔ maj b * (maj (bigStep a) * a * bigStep a) :=
        sup_le_sup_right (mul_le_mul' le_rfl valDiag_le_introDiag) _
    _ ≤ ⊥ ⊔ maj b * (maj (bigStep a) * a * bigStep a) :=
        sup_le_sup_right (maj_mul_introDiag_le_bot _) _
    _ = maj b * (maj (bigStep a) * a * bigStep a) := bot_sup_eq _
    _ = (maj b * maj (bigStep a)) * a * bigStep a := by
        simp only [mul_assoc]
    _ = maj (b * bigStep a) * a * bigStep a := by rw [h_elim_mul]
    _ = maj (b * bigStep a) * (a * bigStep a) := mul_assoc _ _ _
    _ ≤ maj (b * bigStep a) * bigStep a := mul_le_mul' le_rfl (F2 a)

/-- Lemma A.11: the major-slot projection of the value-diagonal composed with
`bigStep a` is bounded by `a * bigStep a`.

**Status.** The signature is preserved verbatim from the paper. As stated,
without additional hypotheses, the inequality does **not** hold in an arbitrary
involutive quantale — the paper's Remark A.8 (opening of Section A.1) globally
assumes `Inv a` throughout the section, and the algebraic step
`maj valDiag * a = a` used in the derivation is exactly `hinv.2`. Downstream
consumers therefore use the private helper `maj_valDiag_mul_bigStep_le_of_inv`
below, which carries the two missing hypotheses. -/
theorem maj_valDiag_mul_bigStep_le (a : α) :
    maj (valDiag : α) * bigStep a ≤ a * bigStep a := by
  sorry

/-- The hypothesised form of Lemma A.11: the paper's Section A.1 (per Remark
A.8) assumes `Inv a` globally, and the derivation of A.11 uses both the closed
fixed-point law and (F10). This helper carries those hypotheses explicitly. -/
private theorem maj_valDiag_mul_bigStep_le_of_inv {a : α}
    (hclosed : a = SRA.box a) (hinv : Inv a) :
    maj (valDiag : α) * bigStep a ≤ a * bigStep a := by
  have hfix : bigStep a = valDiag ⊔ maj (bigStep a) * a * bigStep a :=
    bigStep_fix_of_closed hclosed
  have hF10 : (valDiag : α) * bigStep a = valDiag := F10 a hinv
  have h_elim_mul :
      maj (valDiag : α) * maj (bigStep a) = maj (valDiag : α) := by
    change OperationalDecomposition.elim (valDiag : α) 1
             * OperationalDecomposition.elim (bigStep a) 1
         = OperationalDecomposition.elim (valDiag : α) 1
    rw [← OperationalDecomposition.elim_mul, mul_one, hF10]
  calc maj (valDiag : α) * bigStep a
      = maj (valDiag : α) * (valDiag ⊔ maj (bigStep a) * a * bigStep a) := by
        rw [← hfix]
    _ = maj (valDiag : α) * valDiag
          ⊔ maj (valDiag : α) * (maj (bigStep a) * a * bigStep a) :=
        Quantale.mul_sup_distrib
    _ ≤ maj (valDiag : α) * introDiag
          ⊔ maj (valDiag : α) * (maj (bigStep a) * a * bigStep a) :=
        sup_le_sup_right (mul_le_mul' le_rfl valDiag_le_introDiag) _
    _ ≤ ⊥ ⊔ maj (valDiag : α) * (maj (bigStep a) * a * bigStep a) :=
        sup_le_sup_right (maj_mul_introDiag_le_bot _) _
    _ = maj (valDiag : α) * (maj (bigStep a) * a * bigStep a) := bot_sup_eq _
    _ = (maj (valDiag : α) * maj (bigStep a)) * a * bigStep a := by
        simp only [mul_assoc]
    _ = maj (valDiag : α) * a * bigStep a := by rw [h_elim_mul]
    _ = a * bigStep a := by rw [← hinv.2]

/-- First half of the proof of Theorem A.12 (and Theorem 5.9):
for a closed, invertible, deterministic reduction `a`,
`aᵒ * bigStep a ≤ bigStep a`. The draft's derivation is three steps:
`a° ; a⇓ = a° ; ⟨Δκ⟩ ; a⇓` by Inv, `≤ a° ; a ; a⇓` by Lemma A.11,
`≤ a⇓` by the determinism hypothesis. -/
theorem converse_mul_bigStep_le {a : α} (hclosed : a = SRA.box a) (hinv : Inv a)
    (hdet : IsDeterministicRule a) : aᵒ * bigStep a ≤ bigStep a := by
  have h_valDiag_symm : (valDiag : α)ᵒ = valDiag := by
    change (SRA.box (OperationalDecomposition.intro (1 : α)))ᵒ
         = SRA.box (OperationalDecomposition.intro (1 : α))
    rw [SRA.box_converse, ← OperationalDecomposition.intro_converse,
        IsInvolutiveQuantale.converse_one]
  have h_majVD_symm : (maj (valDiag : α))ᵒ = maj (valDiag : α) := by
    change (OperationalDecomposition.elim (valDiag : α) 1)ᵒ
         = OperationalDecomposition.elim (valDiag : α) 1
    rw [← OperationalDecomposition.elim_converse, h_valDiag_symm,
        IsInvolutiveQuantale.converse_one]
  have h_a_conv : aᵒ = aᵒ * maj (valDiag : α) := by
    have h := congrArg (·ᵒ) hinv.2
    rw [IsInvolutiveQuantale.mul_converse, h_majVD_symm] at h
    exact h
  calc aᵒ * bigStep a
      = aᵒ * maj (valDiag : α) * bigStep a := by rw [← h_a_conv]
    _ = aᵒ * (maj (valDiag : α) * bigStep a) := mul_assoc _ _ _
    _ ≤ aᵒ * (a * bigStep a) :=
        mul_le_mul' le_rfl (maj_valDiag_mul_bigStep_le_of_inv hclosed hinv)
    _ = (aᵒ * a) * bigStep a := (mul_assoc _ _ _).symm
    _ ≤ 1 * bigStep a := mul_le_mul' hdet le_rfl
    _ = bigStep a := one_mul _

/-- Theorem A.12 (and Theorem 5.9 of the body, same statement):
for a reduction `a` that is closed, invertible, and deterministic,
the big-step evaluation satisfies the orthogonality condition
`(bigStep a)ᵒ * bigStep a ≤ valDiag`. The draft's derivation applies
(F9) with `b := valDiag ← bigStep a` and discharges three goals:
the first by (F10), the second by `converse_mul_bigStep_le`, the third
by Proposition A.9 followed by Lemma A.11. -/
theorem determinism {a : α} (_hred : IsReduction a) (hclosed : a = SRA.box a)
    (hinv : Inv a) (hdet : IsDeterministicRule a) :
    (bigStep a)ᵒ * bigStep a ≤ valDiag := by
  have haux : aᵒ * bigStep a ≤ bigStep a :=
    converse_mul_bigStep_le hclosed hinv hdet
  have hb_key :
      (bigStep a ⇨ₗ (valDiag : α)) * bigStep a ≤ (valDiag : α) :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  suffices h : (bigStep a)ᵒ ≤ (bigStep a ⇨ₗ (valDiag : α)) by
    calc (bigStep a)ᵒ * bigStep a
        ≤ (bigStep a ⇨ₗ (valDiag : α)) * bigStep a :=
          mul_le_mul' h le_rfl
      _ ≤ valDiag := hb_key
  refine F9 (a := a) ?_
  refine sup_le (sup_le ?_ ?_) ?_
  · -- (i) `valDiag ≤ b`, i.e. `valDiag * bigStep a ≤ valDiag` by (F10).
    apply Quantale.leftMulResiduation_le_iff_mul_le.mpr
    exact le_of_eq (F10 a hinv)
  · -- (ii) `b * aᵒ ≤ b`, i.e. `b * aᵒ * bigStep a ≤ valDiag`,
    -- from `aᵒ * bigStep a ≤ bigStep a` (Part 1) and `b * bigStep a ≤ valDiag`.
    apply Quantale.leftMulResiduation_le_iff_mul_le.mpr
    calc (bigStep a ⇨ₗ (valDiag : α)) * aᵒ * bigStep a
        = (bigStep a ⇨ₗ (valDiag : α)) * (aᵒ * bigStep a) :=
          mul_assoc _ _ _
      _ ≤ (bigStep a ⇨ₗ (valDiag : α)) * bigStep a :=
          mul_le_mul' le_rfl haux
      _ ≤ valDiag := hb_key
  · -- (iii) `b * maj b ≤ b`, i.e. `b * maj b * bigStep a ≤ valDiag`.
    -- Proposition A.9 rewrites the middle `maj b * bigStep a` to
    -- `maj (b * bigStep a) * bigStep a`; monotonicity of `maj` and
    -- `b * bigStep a ≤ valDiag` bound it by `maj valDiag * bigStep a`;
    -- Lemma A.11 lifts that to `a * bigStep a`; (F2) then absorbs it
    -- into `bigStep a`; finally `b * bigStep a ≤ valDiag` closes.
    apply Quantale.leftMulResiduation_le_iff_mul_le.mpr
    calc (bigStep a ⇨ₗ (valDiag : α))
              * maj (bigStep a ⇨ₗ (valDiag : α)) * bigStep a
        = (bigStep a ⇨ₗ (valDiag : α))
              * (maj (bigStep a ⇨ₗ (valDiag : α)) * bigStep a) :=
          mul_assoc _ _ _
      _ ≤ (bigStep a ⇨ₗ (valDiag : α))
              * (maj ((bigStep a ⇨ₗ (valDiag : α)) * bigStep a) * bigStep a) :=
          mul_le_mul' le_rfl (maj_mul_bigStep_le hclosed hinv _)
      _ ≤ (bigStep a ⇨ₗ (valDiag : α))
              * (maj (valDiag : α) * bigStep a) := by
          refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
          exact elim_mono hb_key le_rfl
      _ ≤ (bigStep a ⇨ₗ (valDiag : α)) * (a * bigStep a) :=
          mul_le_mul' le_rfl
            (maj_valDiag_mul_bigStep_le_of_inv hclosed hinv)
      _ ≤ (bigStep a ⇨ₗ (valDiag : α)) * bigStep a :=
          mul_le_mul' le_rfl (F2 a)
      _ ≤ valDiag := hb_key

#print axioms OperationalDecomposition.IsDeterministicRule
#print axioms OperationalDecomposition.maj_mul_bigStep_le
#print axioms OperationalDecomposition.maj_valDiag_mul_bigStep_le
#print axioms OperationalDecomposition.converse_mul_bigStep_le
#print axioms OperationalDecomposition.determinism

end OperationalDecomposition
