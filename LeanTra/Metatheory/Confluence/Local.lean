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

/-- Observation from the paper's proof sketch of Lemma 6.5: composing an
introduction-form step with parallel reduction stays inside the introduction
layer. -/
theorem intro_mul_parRed_le {a : α} (hgip : GIP a) (x : α) :
    OperationalDecomposition.intro x * parRed a
      ≤ OperationalDecomposition.intro (x * parRed a) := by
  have hfix : parRed a = SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
    SRA.howe_fix _
  have hcr :
      OperationalDecomposition.intro x * SRA.cr (parRed a)
        ≤ OperationalDecomposition.intro x
            * OperationalDecomposition.intro (parRed a) := by
    have hexp :
        OperationalDecomposition.intro x * SRA.cr (parRed a)
          = OperationalDecomposition.intro x * SRA.varDiag
              ⊔ OperationalDecomposition.intro x
                  * OperationalDecomposition.intro (parRed a)
              ⊔ OperationalDecomposition.intro x
                  * OperationalDecomposition.elim (parRed a) (parRed a) := by
      unfold SRA.cr
      rw [OperationalDecomposition.scr_eq_intro_sup_elim,
          Quantale.mul_sup_distrib, Quantale.mul_sup_distrib, sup_assoc]
    rw [hexp]
    refine sup_le (sup_le ?_ le_rfl) ?_
    · calc OperationalDecomposition.intro x * SRA.varDiag
          ≤ SRA.scr x * SRA.varDiag :=
            mul_le_mul' (OperationalDecomposition.intro_le_scr x) le_rfl
        _ ≤ ⊥ := SRA.scr_mul_varDiag_le_bot x
        _ ≤ _ := bot_le
    · exact
        (OperationalDecomposition.intro_mul_elim_le_bot _ _ _).trans bot_le
  have hkillGIP :
      OperationalDecomposition.intro (parRed a) * SRA.subst a 1 ≤ (⊥ : α) := by
    calc OperationalDecomposition.intro (parRed a) * SRA.subst a 1
        ≤ OperationalDecomposition.intro (parRed a)
              * (maj (introDiag : α) * SRA.subst a 1) :=
          mul_le_mul' le_rfl (GIP_substOne hgip)
      _ = OperationalDecomposition.intro (parRed a) * maj (introDiag : α)
              * SRA.subst a 1 := (mul_assoc _ _ _).symm
      _ ≤ (⊥ : α) * SRA.subst a 1 :=
          mul_le_mul' (OperationalDecomposition.intro_mul_elim_le_bot _ _ _) le_rfl
      _ = ⊥ := Quantale.bot_mul
  calc OperationalDecomposition.intro x * parRed a
      = OperationalDecomposition.intro x
            * (SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1)) := by rw [← hfix]
    _ = OperationalDecomposition.intro x * SRA.cr (parRed a)
            * (1 ⊔ SRA.subst a 1) := (mul_assoc _ _ _).symm
    _ ≤ OperationalDecomposition.intro x
            * OperationalDecomposition.intro (parRed a)
            * (1 ⊔ SRA.subst a 1) := mul_le_mul' hcr le_rfl
    _ = OperationalDecomposition.intro x
            * OperationalDecomposition.intro (parRed a)
          ⊔ OperationalDecomposition.intro x
              * OperationalDecomposition.intro (parRed a) * SRA.subst a 1 := by
          rw [Quantale.mul_sup_distrib, mul_one]
    _ ≤ OperationalDecomposition.intro x
            * OperationalDecomposition.intro (parRed a) := by
          refine sup_le le_rfl ?_
          calc OperationalDecomposition.intro x
                  * OperationalDecomposition.intro (parRed a) * SRA.subst a 1
              = OperationalDecomposition.intro x
                  * (OperationalDecomposition.intro (parRed a)
                      * SRA.subst a 1) := mul_assoc _ _ _
            _ ≤ OperationalDecomposition.intro x * (⊥ : α) :=
                mul_le_mul' le_rfl hkillGIP
            _ = ⊥ := Quantale.mul_bot
            _ ≤ _ := bot_le
    _ = OperationalDecomposition.intro (x * parRed a) :=
          (OperationalDecomposition.intro_mul _ _).symm

/-- Paper's Lemma 6.5: `a[Δ]° * ~(a[Δ]⇛) ≤ a°[a⇛]` for any reduction `a`
satisfying (GCP) and (GIP).

**Proof status.** The introduction branch closes; the elimination branch
does not. After splitting `~(a[Δ]⇛) = intro(a⇛) ⊔ elim(a⇛)(a⇛)` via
`parRed_substOne` and `scr_eq_intro_sup_elim`, the introduction branch is
discharged from `GIP_substOne` transposed and `elim_mul_intro_le_bot`. On
the elimination branch, `GIP_substOne` (transposed), the composition law of
`elim`, and `intro_mul_parRed_le` at `x = 1` reduce the goal to
`(SRA.subst a 1)ᵒ * elim (SRA.cr (parRed a)) (parRed a)
  ≤ SRA.subst aᵒ (parRed a)`.
The right-hand factor of the LHS is now exactly the LHS of (GCP) at
`x = parRed a`, but the orientation is wrong twice:

* (GCP) is stated about `a`, while the goal carries `SRA.subst a 1`. The
  substitution axiom `subst (u * v) (b * c) ≤ subst u b * subst v c` is
  oplax the wrong way to lift a fact about `a` to `SRA.subst a 1`.
* The transposed (GCP) at `x = (parRed a)ᵒ`, combined with `parRed_subst_le`,
  produces `parRed a * aᵒ`, while the goal asks for `SRA.subst aᵒ (parRed a)`.
  The `nesting` lemma relates the two in the opposite direction. -/
theorem orthogonality_second_of_gentzen_principles {a : α}
    (hred : IsReduction a)
    (hgcp : GCP a)
    (hgip : GIP a) :
    (SRA.subst a 1)ᵒ * SRA.scr (parRed (SRA.subst a 1)) ≤ SRA.subst aᵒ (parRed a) := by
  rw [parRed_substOne, OperationalDecomposition.scr_eq_intro_sup_elim, Quantale.mul_sup_distrib]
  refine sup_le ?_ ?_
  · have hgipT :
        (SRA.subst a 1)ᵒ
          ≤ (SRA.subst a 1)ᵒ * (maj (introDiag : α))ᵒ := by
      have h := IsInvolutiveQuantale.converse_le_converse (GIP_substOne hgip)
      rwa [IsInvolutiveQuantale.mul_converse] at h
    have hkill :
        (maj (introDiag : α))ᵒ * OperationalDecomposition.intro (parRed a)
          ≤ (⊥ : α) := by
      have : (OperationalDecomposition.elim (introDiag : α) 1)ᵒ
                * OperationalDecomposition.intro (parRed a) ≤ ⊥ := by
        rw [← OperationalDecomposition.elim_converse]
        exact OperationalDecomposition.elim_mul_intro_le_bot _ _ _
      exact this
    calc (SRA.subst a 1)ᵒ * OperationalDecomposition.intro (parRed a)
        ≤ (SRA.subst a 1)ᵒ * (maj (introDiag : α))ᵒ
              * OperationalDecomposition.intro (parRed a) :=
          mul_le_mul' hgipT le_rfl
      _ = (SRA.subst a 1)ᵒ
              * ((maj (introDiag : α))ᵒ
                  * OperationalDecomposition.intro (parRed a)) := mul_assoc _ _ _
      _ ≤ (SRA.subst a 1)ᵒ * (⊥ : α) := mul_le_mul' le_rfl hkill
      _ = ⊥ := Quantale.mul_bot
      _ ≤ SRA.subst aᵒ (parRed a) := bot_le
  · have hgipT :
        (SRA.subst a 1)ᵒ
          ≤ (SRA.subst a 1)ᵒ * (maj (introDiag : α))ᵒ := by
      have h := IsInvolutiveQuantale.converse_le_converse (GIP_substOne hgip)
      rwa [IsInvolutiveQuantale.mul_converse] at h
    have hmajSelf : (maj (introDiag : α))ᵒ = maj (introDiag : α) := by
      change (OperationalDecomposition.elim (introDiag : α) 1)ᵒ
              = OperationalDecomposition.elim (introDiag : α) 1
      rw [← OperationalDecomposition.elim_converse,
          IsInvolutiveQuantale.converse_one]
      congr 1
      change (OperationalDecomposition.intro (1 : α))ᵒ
              = OperationalDecomposition.intro (1 : α)
      rw [← OperationalDecomposition.intro_converse,
          IsInvolutiveQuantale.converse_one]
    have hmulExpand :
        maj (introDiag : α)
          * OperationalDecomposition.elim (parRed a) (parRed a)
        = OperationalDecomposition.elim ((introDiag : α) * parRed a) (parRed a) := by
      change OperationalDecomposition.elim (introDiag : α) 1
              * OperationalDecomposition.elim (parRed a) (parRed a) = _
      rw [← OperationalDecomposition.elim_mul, one_mul]
    have hkey :
        (SRA.subst a 1)ᵒ
              * OperationalDecomposition.elim (parRed a) (parRed a)
          ≤ (SRA.subst a 1)ᵒ
              * OperationalDecomposition.elim
                  (SRA.cr (parRed a)) (parRed a) := by
      calc (SRA.subst a 1)ᵒ
              * OperationalDecomposition.elim (parRed a) (parRed a)
          ≤ (SRA.subst a 1)ᵒ * (maj (introDiag : α))ᵒ
                * OperationalDecomposition.elim (parRed a) (parRed a) :=
              mul_le_mul' hgipT le_rfl
        _ = (SRA.subst a 1)ᵒ
                * (maj (introDiag : α)
                    * OperationalDecomposition.elim (parRed a) (parRed a)) := by
              rw [mul_assoc, hmajSelf]
        _ = (SRA.subst a 1)ᵒ
                * OperationalDecomposition.elim
                    ((introDiag : α) * parRed a) (parRed a) := by
              rw [hmulExpand]
        _ ≤ (SRA.subst a 1)ᵒ
                * OperationalDecomposition.elim
                    (OperationalDecomposition.intro (parRed a)) (parRed a) := by
              refine mul_le_mul' le_rfl (elim_mono ?_ le_rfl)
              have := intro_mul_parRed_le hgip (1 : α)
              rw [one_mul] at this
              exact this
        _ ≤ (SRA.subst a 1)ᵒ
                * OperationalDecomposition.elim
                    (SRA.cr (parRed a)) (parRed a) := by
              refine mul_le_mul' le_rfl (elim_mono ?_ le_rfl)
              exact (OperationalDecomposition.intro_le_scr _).trans le_sup_right
    refine hkey.trans ?_
    show (SRA.subst a 1)ᵒ
            * OperationalDecomposition.elim (SRA.cr (parRed a)) (parRed a)
          ≤ SRA.subst aᵒ (parRed a)
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
    (hgcp : GCP a)
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
