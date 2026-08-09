/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.OperationalDecomposition
public import LeanTra.Metatheory.Confluence.Orthogonal

/-!
# Local conditions and the bridge to confluence of parallel reduction

The compatibility, substitutivity, and deterministic-reduction predicates,
the Gentzen Conservation Principle, two auxiliary substitution/orthogonality
lemmas, the paper's Lemma 6.5 (deriving the second orthogonality conjunct
from the Gentzen principles) and the paper's Theorem 6.6, conclusion (i)
(confluence of parallel reduction from the local conditions).

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Lemma 6.5 and Theorem 6.6, conclusion (i).
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA LeanTra.Confluence

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

open OperationalDecomposition

/-- A relation `x` is *compatible* when the compatible refinement of `x`
refines `x`: `hat x ≤ x`. -/
def IsCompatible (x : α) : Prop := SRA.cr x ≤ x

/-- A relation `a` is *substitutive* when substituting `a`-related terms
into an `a`-related term stays `a`-related: `a[a] ≤ a`. -/
def IsSubstitutive (a : α) : Prop := SRA.subst a a ≤ a

/-- A reduction `a` is *deterministic* when its base substitution instance
`a[Δ]` satisfies `a[Δ]° * a[Δ] ≤ Δ`; the two ends of a rewrite of the same
term agree up to renaming. This is the paper's first orthogonality
condition. -/
def IsDeterministicReduction (a : α) : Prop :=
  (SRA.subst a 1)ᵒ * SRA.subst a 1 ≤ 1

/-- The Gentzen Conservation Principle for `a`: for every compatible `x`, the
composite `elim (hat x) x * a` factors on the right through the substitution
`x[x]` following `a`. -/
def SatisfiesGentzenConservation (a : α) : Prop :=
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

/-- Paper's Lemma 6.5: `a[Δ]° * ~(a[Δ]⇛) ≤ a°[a⇛]` for any reduction `a`
satisfying (GCP) and (GIP).

**Proof status.** Not proved here. The two lemmas above reduce the goal,
in converse form and after `parRed_substOne`, to
`elim ((parRed a)ᵒ * introDiag) ((parRed a)ᵒ) * SRA.subst a 1
  ≤ SRA.subst a ((parRed a)ᵒ)`. Instantiating (GCP) at `x = (parRed a)ᵒ`
gives `elim (hat x) x * a ≤ a * x[x]`, and `x[x] ≤ x` there by
substitutivity of parallel reduction. Three mismatches remain: `x * introDiag`
against `hat x` in the first argument of `elim`; `SRA.subst a 1` against `a`;
and `SRA.subst a x` against `a * x`. The paper's proof sketch is a one-line
argument whose glyphs do not survive extraction from the PDF. -/
theorem orthogonality_second_of_gentzen_principles {a : α}
    (hred : IsReduction a)
    (hgcp : SatisfiesGentzenConservation a)
    (hgip : GIP a) :
    (SRA.subst a 1)ᵒ * SRA.scr (parRed (SRA.subst a 1))
      ≤ SRA.subst aᵒ (parRed a) := by
  sorry

/-- Paper's Theorem 6.6, conclusion (i): a substitutive and deterministic
reduction that satisfies (GCP) and (GIP) has confluent parallel reduction.

**On `hsub`.** The paper states the theorem with substitutivity of `a` as a
standing hypothesis for all three conclusions; conclusion (i) alone does not
consume it. It is kept in the signature to match the paper.

**Dependency on `sorry`.** This theorem is proved from
`orthogonality_second_of_gentzen_principles` (via `parRed_substOne`) together
with `hdet`, so it inherits the `sorryAx` dependency of the former. -/
theorem confluent_parallelReduction_of_gentzen_principles {a : α}
    (hred : IsReduction a)
    (hsub : IsSubstitutive a)
    (hdet : IsDeterministicReduction a)
    (hgcp : SatisfiesGentzenConservation a)
    (hgip : GIP a) :
    Confluent (parRed a) :=
  confluent_parRed hred
    ⟨hdet, by
      have h := orthogonality_second_of_gentzen_principles hred hgcp hgip
      rwa [parRed_substOne] at h⟩

end LeanTra.Confluence

#print axioms LeanTra.Confluence.GIP_substOne
#print axioms LeanTra.Confluence.scr_mul_majIntroDiag
#print axioms LeanTra.Confluence.orthogonality_second_of_gentzen_principles
#print axioms LeanTra.Confluence.confluent_parallelReduction_of_gentzen_principles
#print axioms LeanTra.Confluence.confluent_parRed
#print axioms LeanTra.Confluence.diamond_parRed
