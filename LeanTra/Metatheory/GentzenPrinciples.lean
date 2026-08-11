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
def GIP (a : α) : Prop := a ≤ maj (introDiag : α) * a

/-- Invariance under the value modality: `a` is closed and factors on
the left through the major-slot projection of the closed-values
relation. -/
def Inv (a : α) : Prop := a = SRA.box a ∧ a = maj (valDiag : α) * a

/-- Under the Gentzen Inversion Principle, composing an introduction on
the left with a GIP relation on the right lands in `⊥`. -/
theorem intro_mul_of_gip {a : α} (hGIP : GIP a) (x : α) :
    OperationalDecomposition.intro x * a ≤ (⊥ : α) := by
  calc OperationalDecomposition.intro x * a
      ≤ OperationalDecomposition.intro x
          * (maj (introDiag : α) * a) := by
        exact mul_le_mul' le_rfl hGIP
    _ = OperationalDecomposition.intro x
          * maj (introDiag : α) * a := by
        rw [mul_assoc]
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.intro x
              * OperationalDecomposition.elim (introDiag : α) 1 ≤ ⊥
        exact OperationalDecomposition.intro_mul_elim_le_bot _ _ _
    _ = ⊥ := Quantale.bot_mul

end OperationalDecomposition

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

open OperationalDecomposition

/-- The Gentzen Conservation Principle for `a`: for every compatible `x`, the
composite `elim (hat x) x * a` factors on the right through the substitution
`x[x]` following `a`. -/
def GCP (a : α) : Prop :=
  ∀ x, IsCompatible x →
    OperationalDecomposition.elim (SRA.cr x) x * a ≤ a * SRA.subst x x

/-- Gentzen's Inversion Principle survives passing to the base substitution
instance: from `GIP a`, the substituted relation `a[Δ]` still factors on the
left through `maj introDiag`. -/
theorem GIP_substOne {a : α} (h : GIP a) :
    SRA.subst a 1 ≤ maj (introDiag : α) * SRA.subst a 1 := by
  have hmaj : SRA.subst (maj (introDiag : α)) 1 ≤ maj (introDiag : α) := by
    have h1 : SRA.subst (OperationalDecomposition.intro (1 : α)) 1
                ≤ OperationalDecomposition.intro (1 : α) :=
      (OperationalDecomposition.subst_intro_le _ _).trans
        (by rw [SRA.subst_one_one])
    calc SRA.subst (maj (introDiag : α)) 1
        = SRA.subst (OperationalDecomposition.elim
              (OperationalDecomposition.intro (1 : α)) 1) 1 := rfl
      _ ≤ OperationalDecomposition.elim
              (SRA.subst (OperationalDecomposition.intro (1 : α)) 1)
              (SRA.subst (1 : α) 1) :=
            OperationalDecomposition.subst_elim_le _ _ _
      _ ≤ OperationalDecomposition.elim
              (OperationalDecomposition.intro (1 : α)) 1 :=
            elim_mono h1 (le_of_eq SRA.subst_one_one)
  calc SRA.subst a 1
      ≤ SRA.subst (maj (introDiag : α) * a) 1 := SRA.subst_mono_left h
    _ = SRA.subst (maj (introDiag : α) * a) (1 * 1) := by rw [mul_one]
    _ ≤ SRA.subst (maj (introDiag : α)) 1 * SRA.subst a 1 :=
          SRA.subst_mul_le _ _ _ _
    _ ≤ maj (introDiag : α) * SRA.subst a 1 := mul_le_mul' hmaj le_rfl

/-- Composite of the strict compatible refinement with the major-argument
diagonal on introduction forms: `~x * ⟨‾Δ⟩ = ⟨x * ‾Δ, x⟩`. The introduction
summand of `~x` is killed by orthogonality with `‾Δ`; the elimination
summand recombines through the composition law of `elim`. -/
theorem scr_mul_majIntroDiag (x : α) :
    SRA.scr x * maj (introDiag : α)
      = OperationalDecomposition.elim (x * introDiag) x := by
  have hkey : OperationalDecomposition.elim x x
                * OperationalDecomposition.elim (introDiag : α) 1
              = OperationalDecomposition.elim (x * introDiag) x := by
    rw [← OperationalDecomposition.elim_mul, mul_one]
  rw [OperationalDecomposition.scr_eq_intro_sup_elim, Quantale.sup_mul_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · exact (OperationalDecomposition.intro_mul_elim_le_bot _ _ _).trans bot_le
    · exact hkey.le
  · exact le_sup_of_le_right hkey.ge

/-- Under the invariance hypothesis `Inv a`, composing the value-diagonal
on the left with `a` lands in `⊥`. The draft's derivation is
`Δκ ; a = Δκ ; ⟨Δκ⟩ ; a ≤ ‾Δ ; ⟨Δκ⟩ ; a = ⊥`, the last step by
orthogonality of intro and elim. -/
theorem valDiag_mul_le_bot_of_inv {a : α} (h : Inv a) : valDiag * a ≤ ⊥ := by
  rcases h with ⟨hclosed, hinv⟩
  have h_eq : valDiag * a = valDiag * (maj (valDiag : α) * a) :=
    congrArg (fun x => valDiag * x) hinv
  rw [h_eq]
  calc valDiag * (maj (valDiag : α) * a)
      = (valDiag * maj (valDiag : α)) * a := by rw [mul_assoc]
    _ ≤ (introDiag * maj (valDiag : α)) * a :=
        mul_le_mul' (mul_le_mul' valDiag_le_introDiag le_rfl) le_rfl
    _ = ((OperationalDecomposition.intro 1 : α) * OperationalDecomposition.elim (valDiag : α) 1) * a := rfl
    _ ≤ (⊥ : α) * a :=
        mul_le_mul' (OperationalDecomposition.intro_mul_elim_le_bot 1 (valDiag : α) 1) le_rfl
    _ = ⊥ := Quantale.bot_mul

#print axioms LeanTra.Confluence.valDiag_mul_le_bot_of_inv

end LeanTra.Confluence
