/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.InvolutiveQuantale
public import Mathlib.Order.FixedPoints

/-!
# The Kleene star and its converse in a unital quantale

The Kleene star `a∗` of an element of a unital quantale, defined as the least
fixed point of `x ↦ 1 ⊔ a * x`. Read relationally, `a∗` is the
reflexive-transitive closure of `a`, and the laws below are the standard ones.

The construction needs only `Monoid`, `CompleteLattice` and `IsQuantale`. The
involution is required by the last section alone, where converse is shown to
commute with the star.

## Implementation notes

Mathlib supplies `Mathlib.Algebra.Order.Kleene.KleeneAlgebra`, an idempotent
semiring with a Kleene star. Reusing it here would force `+ := ⊔`, `0 := ⊥`,
and a `Semiring` structure on `α`, creating instance-diamond risk against
the existing `CompleteLattice`. We instead define `star` directly as the
least fixed point of `x ↦ 1 ⊔ a * x` via `OrderHom.lfp`. Every Kleene-star
law we need falls out of `map_lfp` / `lfp_le`, with no algebraic refactor of
the ambient structure.

## References

* Georg Struth. *Calculating Church-Rosser proofs in Kleene algebra.* RelMICS 2001.
* Georg Struth. *Abstract abstract reduction.* JLAMP 2006.
-/
@[expose] public section

open scoped Quantale

namespace LeanTra.Algebra

section Quantale

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
variable {a b : α}

/-! ### Definition and fixed-point interface

`star` is the least fixed point of the left-handed recursor, so its
characteristic equation and its induction principle are `map_lfp` and `lfp_le`
read through the definition. Everything below follows from these two. -/

/-- The recursor `x ↦ 1 ⊔ a * x`, bundled as an `OrderHom` so that
`OrderHom.lfp` applies to it. -/
def starRecursorLeft (a : α) : α →o α where
  toFun x := 1 ⊔ a * x
  monotone' _ _ h := sup_le_sup_left (mul_le_mul_right h a) 1

/-- The Kleene star `a∗`: the least solution of `x = 1 ⊔ a * x`. Relationally,
sequences of `a`-steps of any length, the empty one included. -/
def star (a : α) : α := (starRecursorLeft a).lfp

@[inherit_doc]
scoped postfix:max "∗" => LeanTra.Algebra.star

/-- Unfolding: an `a∗`-sequence is either empty or an `a`-step followed by
another one. -/
theorem star_fixpoint (a : α) : a∗ = 1 ⊔ a * a∗ :=
  ((starRecursorLeft a).map_lfp).symm

/-- Induction on the length of an `a∗`-sequence: anything closed under both
the empty sequence and one further `a`-step already contains `a∗`. -/
theorem star_induction {a x : α} (h : 1 ⊔ a * x ≤ x) : a∗ ≤ x :=
  (starRecursorLeft a).lfp_le h

/-! ### Basic laws

`a∗` contains the identity and `a`, absorbs `a` on either side, and is
transitive, idempotent and monotone. -/

/-- The empty sequence. -/
theorem star_reflexivity (a : α) : 1 ≤ a∗ := by
  conv_rhs => rw [star_fixpoint]
  exact le_sup_left

/-- The one-step sequences: a single `a`-step is an `a∗`-sequence. -/
theorem star_extensivity (a : α) : a ≤ a∗ := by
  conv_rhs => rw [star_fixpoint]
  refine le_sup_of_le_right ?_
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * a∗ := mul_le_mul_right (star_reflexivity a) a

/-- Prefixing an `a`-step to an `a∗`-sequence gives an `a∗`-sequence. -/
theorem star_absorption_left (a : α) : a * a∗ ≤ a∗ := by
  conv_rhs => rw [star_fixpoint]
  exact le_sup_right

/-- Appending an `a`-step to an `a∗`-sequence gives an `a∗`-sequence. The
mirror of `star_absorption_left`, and what makes the right-handed recursor
land on `a∗` too. -/
theorem star_absorption_right (a : α) : a∗ * a ≤ a∗ := by
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine star_induction ?_
  refine sup_le ?_ ?_
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    rw [one_mul]; exact star_extensivity a
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    calc a * (a ⇨ₗ a∗) * a
        = a * ((a ⇨ₗ a∗) * a) := mul_assoc _ _ _
      _ ≤ a * a∗ := mul_le_mul_right
          (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl) a
      _ ≤ a∗ := star_absorption_left a

/-- Enlarging a relation enlarges its closure. -/
theorem star_monotonicity (h : a ≤ b) : a∗ ≤ b∗ := by
  refine star_induction ?_
  refine sup_le (star_reflexivity b) ?_
  calc a * b∗
      ≤ b * b∗ := mul_le_mul_left h _
    _ ≤ b∗ := star_absorption_left b

/-- Concatenating two `a∗`-sequences gives an `a∗`-sequence. -/
theorem star_transitivity (a : α) : a∗ * a∗ ≤ a∗ := by
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine star_induction ?_
  refine sup_le ?_ ?_
  · exact Quantale.leftMulResiduation_le_iff_mul_le.mpr (by rw [one_mul])
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    calc a * (a∗ ⇨ₗ a∗) * a∗
        = a * ((a∗ ⇨ₗ a∗) * a∗) := mul_assoc _ _ _
      _ ≤ a * a∗ := mul_le_mul_right
          (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl) a
      _ ≤ a∗ := star_absorption_left a

/-- Closing an already closed relation adds nothing. -/
theorem star_idempotence (a : α) : a∗∗ = a∗ := by
  refine le_antisymm ?_ (star_extensivity _)
  exact star_induction (sup_le (star_reflexivity a) (star_transitivity a))

/-- The identity is already closed: iterating it produces nothing new. -/
@[simp]
theorem star_identity : (1 : α)∗ = 1 := by
  refine le_antisymm ?_ (star_reflexivity _)
  refine star_induction ?_
  rw [one_mul]
  exact sup_le le_rfl le_rfl

/-- Anything caught between a relation and its closure has the same closure.
Transfers closure properties across such a pair — in a rewriting setting,
between single-step and parallel reduction. -/
theorem star_sandwich (hab : a ≤ b) (hb : b ≤ a∗) : b∗ = a∗ := by
  refine le_antisymm ?_ (star_monotonicity hab)
  calc b∗ ≤ (a∗)∗ := star_monotonicity hb
    _ = a∗ := star_idempotence a

/-! ### Right-handed characterisation

The recursor `x ↦ 1 ⊔ x * a` has the same least fixed point as the left-handed
one. Consumed by `star_converse_commutation`, which exchanges the two. -/

/-- The recursor `x ↦ 1 ⊔ x * a`, appending on the right where
`starRecursorLeft` prepends on the left. -/
def starRecursorRight (a : α) : α →o α where
  toFun x := 1 ⊔ x * a
  monotone' _ _ h := sup_le_sup_left (mul_le_mul_left h a) 1

/-- Building sequences from the right yields the same closure as building them
from the left. Needed because converse turns one construction into the other. -/
theorem star_right_characterisation (a : α) : a∗ = (starRecursorRight a).lfp := by
  set r := (starRecursorRight a).lfp
  have r_fix : r = 1 ⊔ r * a := ((starRecursorRight a).map_lfp).symm
  have one_le_r : (1 : α) ≤ r := by
    conv_rhs => rw [r_fix]
    exact le_sup_left
  have r_mul_le_r : r * a ≤ r := by
    conv_rhs => rw [r_fix]
    exact le_sup_right
  have a_mul_r_le_r : a * r ≤ r := by
    refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
    refine (starRecursorRight a).lfp_le ?_
    refine sup_le ?_ ?_
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      rw [mul_one]
      calc a = 1 * a := (one_mul a).symm
        _ ≤ r * a := mul_le_mul_left one_le_r a
        _ ≤ r := r_mul_le_r
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      calc a * ((a ⇨ᵣ r) * a)
          = (a * (a ⇨ᵣ r)) * a := (mul_assoc _ _ _).symm
        _ ≤ r * a := mul_le_mul_left
            (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl) a
        _ ≤ r := r_mul_le_r
  refine le_antisymm ?_ ?_
  · exact star_induction (sup_le one_le_r a_mul_r_le_r)
  · exact (starRecursorRight a).lfp_le (sup_le (star_reflexivity a) (star_absorption_right a))

end Quantale

section InvolutiveQuantale

open scoped IsInvolutiveQuantale

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]

/-! ### Converse

The involution is used here and nowhere else in the file. -/

/-- Reversing each step of an `a∗`-sequence, and reversing their order, gives
an `aᵒ∗`-sequence. -/
@[simp]
theorem star_converse_commutation (a : α) : (a∗)ᵒ = (aᵒ)∗ := by
  have h : ∀ b : α, (b∗)ᵒ = 1 ⊔ (b∗)ᵒ * bᵒ := fun b => by
    conv_lhs => rw [star_fixpoint b]
    rw [IsInvolutiveQuantale.converse_join_preservation_binary, IsInvolutiveQuantale.converse_identity,
        IsInvolutiveQuantale.converse_compositionality]
  have ge : (aᵒ)∗ ≤ (a∗)ᵒ := by
    rw [star_right_characterisation]
    exact (starRecursorRight aᵒ).lfp_le (h a).ge
  have ge' : ((aᵒ)ᵒ)∗ ≤ ((aᵒ)∗)ᵒ := by
    rw [star_right_characterisation]
    exact (starRecursorRight ((aᵒ)ᵒ)).lfp_le (h aᵒ).ge
  rw [IsInvolutiveQuantale.converse_involutivity] at ge'
  have le : (a∗)ᵒ ≤ (aᵒ)∗ := by
    have := IsInvolutiveQuantale.converse_monotonicity ge'
    simpa [IsInvolutiveQuantale.converse_involutivity] using this
  exact le_antisymm le ge

end InvolutiveQuantale

end LeanTra.Algebra
