/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.KleeneStar

/-!
# Diamond and confluence

The diamond property and confluence for an abstract rewriting relation in
a unital involutive quantale, layered on top of the Kleene-star theory in
`Algebra/KleeneStar.lean`. Provides `Diamond`, `Confluent`, the strip
lemma `Diamond.strip`, and the main implication `Diamond.confluent`, all
consumed by the orthogonal-reduction development in
`Confluence/Orthogonal.lean`.

## References

* Georg Struth. *Calculating Church-Rosser proofs in Kleene algebra.*
  RelMICS 2001.
* Georg Struth. *Abstract abstract reduction.* JLAMP 2006.
* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Theorem 21.
-/
@[expose] public section

open scoped Quantale IsInvolutiveQuantale LeanTra.Algebra

open LeanTra.Algebra

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable {a : α}

/-- The diamond property: `aᵒ * a ≤ a * aᵒ`. -/
def Diamond (a : α) : Prop := aᵒ * a ≤ a * aᵒ

/-- Confluence: the star has the diamond property. -/
def Confluent (a : α) : Prop := Diamond (a∗)

/-- Strip lemma: from the diamond property of `a`, the one-sided propagation
`aᵒ * a∗ ≤ a∗ * aᵒ`. -/
theorem Diamond.strip {a : α} (hd : Diamond a) : aᵒ * a∗ ≤ a∗ * aᵒ := by
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine star_induction ?_
  refine sup_le ?_ ?_
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    rw [mul_one]
    calc aᵒ = 1 * aᵒ := (one_mul aᵒ).symm
      _ ≤ a∗ * aᵒ := mul_le_mul_left (star_reflexivity a) aᵒ
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    calc aᵒ * (a * (aᵒ ⇨ᵣ (a∗ * aᵒ)))
        = (aᵒ * a) * (aᵒ ⇨ᵣ (a∗ * aᵒ)) := (mul_assoc _ _ _).symm
      _ ≤ (a * aᵒ) * (aᵒ ⇨ᵣ (a∗ * aᵒ)) := mul_le_mul_left hd _
      _ = a * (aᵒ * (aᵒ ⇨ᵣ (a∗ * aᵒ))) := mul_assoc _ _ _
      _ ≤ a * (a∗ * aᵒ) := mul_le_mul_right
          (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl) a
      _ = (a * a∗) * aᵒ := (mul_assoc _ _ _).symm
      _ ≤ a∗ * aᵒ := mul_le_mul_left (star_absorption_left a) aᵒ

/-- If `a` has the diamond property, so does `a∗`. -/
theorem Diamond.confluent {a : α} (hd : Diamond a) : Confluent a := by
  change (a∗)ᵒ * a∗ ≤ a∗ * (a∗)ᵒ
  rw [star_converse_commutation]
  have hstrip := hd.strip
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine star_induction ?_
  refine sup_le ?_ ?_
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    rw [one_mul]
    calc a∗ = a∗ * 1 := (mul_one _).symm
      _ ≤ a∗ * (aᵒ)∗ := mul_le_mul_right (star_reflexivity aᵒ) _
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    calc (aᵒ * (a∗ ⇨ₗ (a∗ * (aᵒ)∗))) * a∗
        = aᵒ * ((a∗ ⇨ₗ (a∗ * (aᵒ)∗)) * a∗) := mul_assoc _ _ _
      _ ≤ aᵒ * (a∗ * (aᵒ)∗) := mul_le_mul_right
          (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl) aᵒ
      _ = (aᵒ * a∗) * (aᵒ)∗ := (mul_assoc _ _ _).symm
      _ ≤ (a∗ * aᵒ) * (aᵒ)∗ := mul_le_mul_left hstrip _
      _ = a∗ * (aᵒ * (aᵒ)∗) := mul_assoc _ _ _
      _ ≤ a∗ * (aᵒ)∗ := mul_le_mul_right (star_absorption_left aᵒ) _

end LeanTra.Confluence

#print axioms LeanTra.Confluence.Diamond.confluent
