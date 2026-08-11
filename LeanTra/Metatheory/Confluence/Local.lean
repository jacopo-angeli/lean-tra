/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.Modular
public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Metatheory.Confluence.Orthogonal

/-!
# Local conditions and the bridge to confluence of parallel reduction

Ports the paper's Lemma 6.5 (deriving the second orthogonality conjunct
from the Gentzen principles) and Theorem 6.6, conclusion (i) (confluence
of parallel reduction from the local conditions). The compatibility,
substitutivity, and deterministic-reduction predicates as well as the
Gentzen Conservation Principle live upstream in `Reduction.lean` and
`GentzenPrinciples.lean` and are consumed here from those files.

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
  The `nesting` lemma relates the two in the opposite direction.

Adding `[IsModularQuantale α]` does not touch either obstruction: the
modular law interacts with composition, meet, and converse, but the
remaining step is entirely on the substitution side, and no meet is left
in play. The `sorry` stands. -/
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

#print axioms LeanTra.Confluence.intro_mul_parRed_le
#print axioms LeanTra.Confluence.orthogonality_second_of_gentzen_principles
#print axioms LeanTra.Confluence.confluent_parallelReduction_of_gentzen_principles
