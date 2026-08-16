/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.KleeneStar

/-!
# The diamond property and confluence

Abstract rewriting in a unital involutive quantale, with no reference to
the elements being rewritten. A relation `a` has the *diamond property*
when `aᵒ * a ≤ a * aᵒ`: reading composition as "there exists an
intermediate", the left-hand side relates any two terms reachable from a
common source in one `a`-step each, and the right-hand side asserts that
they have a common reduct, again in one step each. *Confluence* is the
same property of the reflexive-transitive closure `a∗`, so it says the
same thing with "in one step" weakened to "in any number of steps".

Everything here rests on the Kleene star of `Algebra/KleeneStar.lean`,
and the involution supplies the converse `·ᵒ` that turns "reachable from"
into "reaches". Nothing in the file mentions terms, substitution or
syntax: the argument is the standard Kleene-algebra one, and it applies
unchanged to whatever the elements of the quantale happen to be.

## The argument

Confluence does not follow from the diamond property by a single
induction, because closing a diamond over an `a∗`-sequence on one side
still leaves an `a∗`-sequence on the other. It is proved in two passes.
The strip lemma widens one side, propagating a single `a`-step past a
whole `a∗`-sequence; confluence then widens the other, propagating an
`a∗`-sequence past an `a∗`-sequence, and uses the strip lemma as its
induction step. Both passes are the same manoeuvre: residuate to expose a
star, apply `star_induction`, and discharge the two cases.

## References

* Georg Struth. *Calculating Church-Rosser proofs in Kleene algebra.*
  RelMICS 2001.
* Georg Struth. *Abstract abstract reduction.* JLAMP 2006.
-/

@[expose] public section

open scoped Quantale IsInvolutiveQuantale

namespace LeanTra.Algebra

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]


/-! ### The two properties

`IsConfluent` is not a separate notion: it is `IsDiamond` applied to the
reflexive-transitive closure. Stating it that way is what lets the whole
development be a single lemma about `IsDiamond` plus one closure step. -/

/-- The diamond property: `aᵒ * a ≤ a * aᵒ`. Two terms reachable from a
common source in one `a`-step each have a common reduct, again in one
`a`-step each. -/
def IsDiamond (a : α) : Prop := aᵒ * a ≤ a * aᵒ
/-- Confluence: the diamond property of `a∗`. The Church–Rosser property,
with "one step" replaced by "any number of steps" on all four sides. -/
def IsConfluent (a : α) : Prop := IsDiamond (a∗)



/-! ### From the diamond property to confluence

Two propagations of the same shape. `strip` moves a single converse step
past an `a∗`-sequence, `confluent` moves an `a∗`-sequence past an
`a∗`-sequence and consumes `strip` as its inductive step. In both, the
residual turns the goal into a statement of the form `a∗ ≤ x`, which
`star_induction` reduces to the empty sequence and one further step. -/

/-- Strip lemma: `aᵒ * a∗ ≤ a∗ * aᵒ`. A single `a`-step taken backwards
can be pushed past an arbitrary `a∗`-sequence, at the cost of lengthening
that sequence. The one-sided half of confluence, and the step the full
induction runs on. -/
theorem IsDiamond.strip {a : α} (hd : IsDiamond a) : aᵒ * a∗ ≤ a∗ * aᵒ := by
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
/-- The diamond property propagates to the closure. Uses
`star_converse_commutation` to rewrite `(a∗)ᵒ` as `(aᵒ)∗`, so that the
goal is again a statement about a star and `star_induction` applies, with
`strip` discharging the inductive case. -/
theorem IsDiamond.confluent {a : α} (hd : IsDiamond a) : IsConfluent a := by
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

end LeanTra.Algebra

#print axioms LeanTra.Algebra.IsDiamond.confluent
