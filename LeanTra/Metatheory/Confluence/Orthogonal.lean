/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Confluence.ParallelReduction
public import LeanTra.Algebra.Diamond

/-!
# Confluence of orthogonal reduction

The confluence-of-orthogonal-reduction theorem of the reference, stated
here as: for a reduction `a` whose base substitution instances collapse
on overlaps and whose interaction with the strict compatible refinement
of parallel reduction stays inside a substituted converse, `(a⇛)∗` is
confluent.

Orthogonality is a condition on the rule and on its parallel reduction.
Its first conjunct says two `a⟦Δ⟧`-rewrites of the same term differ only
by variable renaming, `(a⟦Δ⟧)ᵒ * a⟦Δ⟧ ≤ Δ`. Its second conjunct swaps a
base-instance backwards step and a strict compatible refinement of
parallel reduction for a substituted converse, `(a⟦Δ⟧)ᵒ * ~(a⇛) ≤
aᵒ⟦a⇛⟧`. Both are inequalities the diamond argument consumes verbatim;
nothing further about `a⇛` is used than what
`Confluence/ParallelReduction.lean` already provides.

The whole argument is the single theorem `confluent_parRed`. The diamond
property `(a⇛)ᵒ * a⇛ ≤ a⇛ * (a⇛)ᵒ` appears inside it as an intermediate
step, not as a result of its own: it is proved by fixed-point induction
on `(a⇛)ᵒ`, which is the op-Howe extension of `Δ ⊔ aᵒ⟦Δ⟧`, transposed
along the composition residual. The two branches of the induction consume
the two orthogonality conjuncts, and the first conjunct cancels an
`aᵒ * a` that appears in the middle of the two-sided branch. Confluence
then follows from `IsDiamond.confluent` in `Algebra/Diamond.lean`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Theorem 21.
* Francesco Gavazzo. *Allegories of Symbolic Manipulations.* LICS 2023,
  Theorem 6.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA
open LeanTra.Algebra

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-! ### Orthogonality

The hypothesis the theorem below assumes: two conjuncts, each an
inequality relating the base instance `a⟦Δ⟧` to `a⇛`, that together let
the diamond argument go through. -/

/-- `a` is *orthogonal* when `(a⟦Δ⟧)ᵒ * a⟦Δ⟧ ≤ Δ` and
`(a⟦Δ⟧)ᵒ * ~(a⇛) ≤ aᵒ⟦a⇛⟧`. -/
def IsOrthogonal (a : α) : Prop :=
  (SRA.subst a 1)ᵒ * SRA.subst a 1 ≤ 1
    ∧ (SRA.subst a 1)ᵒ * SRA.scr (parRed a) ≤ SRA.subst aᵒ (parRed a)

/-! ### Confluence of orthogonal reduction

The single theorem the file exists to prove. The separators inside it
mark the stages: the second orthogonality conjunct is turned round by
converse, the goal is transposed along `⇨ₗ` and opened by fixed-point
induction on `(a⇛)ᵒ`, the rule is commuted past the compatible
refinements on either side, and the four branches of the resulting join
are discharged. -/

/-- Confluence of parallel reduction: for a reduction `a` satisfying
orthogonality, `IsConfluent (a⇛)`. -/
theorem othogonality_confluence {a : α}
  (h : IsReduction a)
  (horth : IsOrthogonal a) :
  IsConfluent (parRed a) := by
  -- The second conjunct, turned round
  --
  -- The diamond argument needs the second orthogonality conjunct on both
  -- sides. Converse turns `(a⟦Δ⟧)ᵒ * ~(a⇛) ≤ aᵒ⟦a⇛⟧` into the mirror
  -- statement about `(a⇛)ᵒ`, which is what the right-hand branch consumes.
  have hscr : SRA.scr ((parRed a)ᵒ) * SRA.subst a 1
            ≤ SRA.subst a ((parRed a)ᵒ) := by
    have h2 := horth.2
    have := IsInvolutiveQuantale.converse_monotonicity h2
    rw [IsInvolutiveQuantale.converse_compositionality,
        IsInvolutiveQuantale.converse_involutivity,
        SRA.subst_converse_commutation,
        IsInvolutiveQuantale.converse_involutivity,
        ← SRA.scr_converse_commutation] at this
    exact this
  -- Confluence is the diamond property of the star, so the whole of the rest
  -- establishes the diamond property of `a⇛` itself.
  suffices hDiamond : IsDiamond (parRed a) by exact hDiamond.confluent
  -- Transposing and opening the induction
  --
  -- Residuating on the left turns the goal into a statement of the form
  -- `(a⇛)ᵒ ≤ x`, and `(a⇛)ᵒ` is the op-Howe extension of `Δ ⊔ aᵒ⟦Δ⟧`, so
  -- fixed-point induction applies. Transposing back leaves the inductive step.
  change (parRed a)ᵒ * parRed a ≤ parRed a * (parRed a)ᵒ
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  rw [parRed_converse a]
  refine SRA.opHowe_induction ?_
  rw [← parRed_converse a]
  refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
  -- Commuting the rule past the compatible refinements
  --
  -- `hU` is the counit of the residuation, `hmid` collapses the two
  -- refinements into one via multiplicativity of `⌃·`, and the three `H`
  -- facts say that the base instance can be pushed past a compatible
  -- refinement on the left, on the right, and cancelled in the middle.
  have hU : (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a
              ≤ parRed a * (parRed a)ᵒ :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hmid :
      SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a)
        ≤ SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) := by
    calc SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a)
        = SRA.cr ((parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a) :=
            SRA.cr_compositionality _ _
      _ ≤ SRA.cr (parRed a * (parRed a)ᵒ) := SRA.cr_monotonicity hU
      _ = SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) :=
            (SRA.cr_compositionality _ _).symm
  have Hleft :
      SRA.subst aᵒ 1 * SRA.cr (parRed a) ≤ parRed a * SRA.subst aᵒ 1 := by
    unfold SRA.cr
    rw [Quantale.mul_sup_distrib]
    refine sup_le ?_ ?_
    · calc SRA.subst aᵒ 1 * SRA.varDiag
          = (⊥ : α) := subst_one_varDiag_orthogonality h
        _ ≤ parRed a * SRA.subst aᵒ 1 := bot_le
    · have h2 := horth.2
      rw [SRA.subst_one_converse_commutation] at h2
      exact h2.trans (parRed_nesting a)
  have Hright :
      SRA.cr ((parRed a)ᵒ) * SRA.subst a 1
        ≤ SRA.subst a 1 * (parRed a)ᵒ := by
    unfold SRA.cr
    rw [Quantale.sup_mul_distrib]
    refine sup_le ?_ ?_
    · calc SRA.varDiag * SRA.subst a 1
          = (⊥ : α) := varDiag_subst_one_orthogonality h
        _ ≤ SRA.subst a 1 * (parRed a)ᵒ := bot_le
    · exact hscr.trans (parRed_converse_nesting a)
  have Hdet : SRA.subst aᵒ 1 * SRA.subst a 1 ≤ (1 : α) := by
    have h1 := horth.1
    rw [SRA.subst_one_converse_commutation] at h1
    exact h1
  -- The four branches
  --
  -- Unfolding `a⇛` once and distributing leaves a join of four products.
  -- The first is closed by compatibility alone, the second and third by
  -- `Hleft` and `Hright` followed by an unfolding, and the fourth by both at
  -- once, with the first orthogonality conjunct cancelling the middle.
  have hfix : parRed a = SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
    SRA.howe_fixpoint _
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
  · exact mul_le_mul' (parRed_compatibility a) (parRed_converse_compatibility a)
  · calc SRA.subst aᵒ 1 * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
        = SRA.subst aᵒ 1 * SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) :=
            (mul_assoc _ _ _).symm
      _ ≤ parRed a * SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ) :=
            mul_le_mul_left Hleft _
      _ = parRed a * (SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ)) := mul_assoc _ _ _
      _ ≤ parRed a * (parRed a)ᵒ :=
            mul_le_mul_right (parRed_converse_unfolding a) _
  · calc SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) * SRA.subst a 1
        = SRA.cr (parRed a) * (SRA.cr ((parRed a)ᵒ) * SRA.subst a 1) :=
            mul_assoc _ _ _
      _ ≤ SRA.cr (parRed a) * (SRA.subst a 1 * (parRed a)ᵒ) :=
            mul_le_mul_right Hright _
      _ = SRA.cr (parRed a) * SRA.subst a 1 * (parRed a)ᵒ :=
            (mul_assoc _ _ _).symm
      _ ≤ parRed a * (parRed a)ᵒ :=
            mul_le_mul_left (parRed_unfolding a) _
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

end LeanTra.Confluence

#print axioms LeanTra.Confluence.othogonality_confluence
