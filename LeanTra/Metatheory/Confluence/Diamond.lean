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
`Algebra/KleeneStar.lean`.

## Contents

* `Diamond`, `Confluent`.
* Strip lemma `Diamond.strip : Diamond a → aᵒ * star a ≤ star a * aᵒ`
  (Struth's calculation, transported to the quantale via `⇨ᵣ`).
* Main theorem `Diamond.confluent : Diamond a → Confluent a`, second
  induction applying the strip lemma one level up via `⇨ₗ`.

Church-Rosser (`(star a)ᵒ * star a ≤ star (a ⊔ aᵒ)`) is deferred; the
equivalence with `Confluent` is a standard next step but is not needed by
the SRA development.

## References

* Georg Struth. *Calculating Church-Rosser proofs in Kleene algebra.*
  RelMICS 2001.
* Georg Struth. *Abstract abstract reduction.* JLAMP 2006.
* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Theorem 21.
* Francesco Gavazzo. *Allegories of Symbolic Manipulations.* LICS 2023,
  Theorem 6.
-/
@[expose] public section

open scoped Quantale IsInvolutiveQuantale LeanTra.Confluence

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable {a : α}

/-- The diamond property: `aᵒ * a ≤ a * aᵒ`. Abstractly, "if `a` steps back
then forward, it can also step forward then back". -/
def Diamond (a : α) : Prop := aᵒ * a ≤ a * aᵒ

/-- Confluence: the star has the diamond property. -/
def Confluent (a : α) : Prop := Diamond (a∗)

/-- Strip lemma: the diamond property propagates from `a` to `a∗` on one
side. This is the hardest step. Method: express `aᵒ * a∗ ≤ a∗ * aᵒ` as
`a∗ ≤ aᵒ ⇨ᵣ (a∗ * aᵒ)` and apply `star_le_of`; the Diamond hypothesis
discharges the induction step. -/
theorem Diamond.strip {a : α} (hd : Diamond a) : aᵒ * a∗ ≤ a∗ * aᵒ := by
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine star_le_of ?_
  refine sup_le ?_ ?_
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    rw [mul_one]
    calc aᵒ = 1 * aᵒ := (one_mul aᵒ).symm
      _ ≤ a∗ * aᵒ := mul_le_mul_left (one_le_star a) aᵒ
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    calc aᵒ * (a * (aᵒ ⇨ᵣ (a∗ * aᵒ)))
        = (aᵒ * a) * (aᵒ ⇨ᵣ (a∗ * aᵒ)) := (mul_assoc _ _ _).symm
      _ ≤ (a * aᵒ) * (aᵒ ⇨ᵣ (a∗ * aᵒ)) := mul_le_mul_left hd _
      _ = a * (aᵒ * (aᵒ ⇨ᵣ (a∗ * aᵒ))) := mul_assoc _ _ _
      _ ≤ a * (a∗ * aᵒ) := mul_le_mul_right
          (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl) a
      _ = (a * a∗) * aᵒ := (mul_assoc _ _ _).symm
      _ ≤ a∗ * aᵒ := mul_le_mul_left (mul_star_le_star a) aᵒ

/-- Confluence from diamond: if `a` has the diamond property, so does `a∗`.
Rewriting `(a∗)ᵒ = (aᵒ)∗` reduces the goal to `(aᵒ)∗ * a∗ ≤ a∗ * (aᵒ)∗`,
which is a second `star_le_of` induction whose induction step is the strip
lemma at one level up, threaded through `⇨ₗ`. -/
theorem Diamond.confluent {a : α} (hd : Diamond a) : Confluent a := by
  change (a∗)ᵒ * a∗ ≤ a∗ * (a∗)ᵒ
  rw [star_converse]
  have hstrip := hd.strip
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine star_le_of ?_
  refine sup_le ?_ ?_
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    rw [one_mul]
    calc a∗ = a∗ * 1 := (mul_one _).symm
      _ ≤ a∗ * (aᵒ)∗ := mul_le_mul_right (one_le_star aᵒ) _
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    calc (aᵒ * (a∗ ⇨ₗ (a∗ * (aᵒ)∗))) * a∗
        = aᵒ * ((a∗ ⇨ₗ (a∗ * (aᵒ)∗)) * a∗) := mul_assoc _ _ _
      _ ≤ aᵒ * (a∗ * (aᵒ)∗) := mul_le_mul_right
          (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl) aᵒ
      _ = (aᵒ * a∗) * (aᵒ)∗ := (mul_assoc _ _ _).symm
      _ ≤ (a∗ * aᵒ) * (aᵒ)∗ := mul_le_mul_left hstrip _
      _ = a∗ * (aᵒ * (aᵒ)∗) := mul_assoc _ _ _
      _ ≤ a∗ * (aᵒ)∗ := mul_le_mul_right (mul_star_le_star aᵒ) _

-- TODO: Church–Rosser, `(a∗)ᵒ * a∗ ≤ (a ⊔ aᵒ)∗`, and the equivalence
-- `ChurchRosser a ↔ Confluent a`. Standard from here, not needed by the
-- SRA development.

end LeanTra.Confluence

#print axioms LeanTra.Confluence.Diamond.confluent
