/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.OperationalDecomposition
public import LeanTra.Metatheory.Reduction

/-!
# Gentzen inversion and conservation principles

The Gentzen Inversion Principle (`GIP`) and invariance under the value
modality (`Inv`), transported across the base substitution instance;
the Gentzen Conservation Principle (`GCP`) and two auxiliary
substitution/orthogonality lemmas that connect the Gentzen principles
to the confluence of parallel reduction.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Lemma 6.5 and Theorem 6.6, conclusion (i).
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- Gentzen Inversion Principle: every `a`-step factors on the left
through an elimination with an introduction form in the major slot. -/
def GIP (a : α) : Prop := a ≤ majorProjection (introductionCoreflexive : α) * a

/-- Invariance under the value modality: `a` is closed and factors on
the left through the major-slot projection of the closed-values
relation. -/
def Inv (a : α) : Prop :=
  a = SRA.box a ∧ a = majorProjection (valueCoreflexive : α) * a

/-- Under the Gentzen Inversion Principle, composing an introduction on
the left with a GIP relation on the right lands in `⊥`. -/
theorem introduction_mul_of_gip {a : α} (hGIP : GIP a) (x : α) :
    OperationalDecomposition.introduction x * a ≤ (⊥ : α) := by
  calc OperationalDecomposition.introduction x * a
      ≤ OperationalDecomposition.introduction x
          * (majorProjection (introductionCoreflexive : α) * a) := by
        exact mul_le_mul' le_rfl hGIP
    _ = OperationalDecomposition.introduction x
          * majorProjection (introductionCoreflexive : α) * a := by
        rw [mul_assoc]
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.introduction x
              * OperationalDecomposition.elimination
                  (introductionCoreflexive : α) 1 ≤ ⊥
        exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
    _ = ⊥ := Quantale.bot_mul

end OperationalDecomposition

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

open OperationalDecomposition

/-- The Gentzen Conservation Principle for `a`: for every compatible `x`, the
composite `elimination (hat x) x * a` factors on the right through the substitution
`x[x]` following `a`. -/
def GCP (a : α) : Prop :=
  ∀ x, IsCompatible x →
    OperationalDecomposition.elimination (SRA.cr x) x * a ≤ a * SRA.subst x x

/-- Gentzen's Inversion Principle survives passing to the base substitution
instance: from `GIP a`, the substituted relation `a[Δ]` still factors on the
left through `majorProjection introductionCoreflexive`. -/
theorem GIP_substOne {a : α} (h : GIP a) :
    SRA.subst a 1 ≤ majorProjection (introductionCoreflexive : α) * SRA.subst a 1 := by
  have hmaj : SRA.subst (majorProjection (introductionCoreflexive : α)) 1
                ≤ majorProjection (introductionCoreflexive : α) := by
    have h1 : SRA.subst (OperationalDecomposition.introduction (1 : α)) 1
                ≤ OperationalDecomposition.introduction (1 : α) :=
      (OperationalDecomposition.substitution_distribution_introduction _ _).trans
        (by rw [SRA.subst_one_one])
    calc SRA.subst (majorProjection (introductionCoreflexive : α)) 1
        = SRA.subst (OperationalDecomposition.elimination
              (OperationalDecomposition.introduction (1 : α)) 1) 1 := rfl
      _ ≤ OperationalDecomposition.elimination
              (SRA.subst (OperationalDecomposition.introduction (1 : α)) 1)
              (SRA.subst (1 : α) 1) :=
            OperationalDecomposition.substitution_distribution_elimination _ _ _
      _ ≤ OperationalDecomposition.elimination
              (OperationalDecomposition.introduction (1 : α)) 1 :=
            elimination_monotonicity h1 (le_of_eq SRA.subst_one_one)
  calc SRA.subst a 1
      ≤ SRA.subst (majorProjection (introductionCoreflexive : α) * a) 1 :=
        SRA.subst_mono_left h
    _ = SRA.subst (majorProjection (introductionCoreflexive : α) * a) (1 * 1) := by
          rw [mul_one]
    _ ≤ SRA.subst (majorProjection (introductionCoreflexive : α)) 1
          * SRA.subst a 1 :=
          SRA.subst_mul_le _ _ _ _
    _ ≤ majorProjection (introductionCoreflexive : α) * SRA.subst a 1 :=
          mul_le_mul' hmaj le_rfl

/-- Composite of the strict compatible refinement with the major-argument
diagonal on introduction forms: `~x * ⟨‾Δ⟩ = ⟨x * ‾Δ, x⟩`. The introduction
summand of `~x` is killed by orthogonality with `‾Δ`; the elimination
summand recombines through the composition law of `elimination`. -/
theorem scr_mul_majIntroductionCoreflexive (x : α) :
    SRA.scr x * majorProjection (introductionCoreflexive : α)
      = OperationalDecomposition.elimination (x * introductionCoreflexive) x := by
  have hkey : OperationalDecomposition.elimination x x
                * OperationalDecomposition.elimination
                    (introductionCoreflexive : α) 1
              = OperationalDecomposition.elimination
                  (x * introductionCoreflexive) x := by
    rw [← OperationalDecomposition.elimination_morphism_composition, mul_one]
  rw [OperationalDecomposition.cocartesian_decomposition,
      Quantale.sup_mul_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · exact (OperationalDecomposition.introduction_elimination_orthogonality _ _ _).trans
        bot_le
    · exact hkey.le
  · exact le_sup_of_le_right hkey.ge

end LeanTra.Confluence
