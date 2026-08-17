/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Quantale

/-!
# Involutive quantales

Mathlib's `IsQuantale` is a mixin over a semigroup and a complete lattice which
does not fix a unit and does not carry an involution. We enrich it by working
over `Monoid` and introducing a single new datum, the converse operation `·ᵒ`.

The involution is governed by four laws:
1. involutivity `aᵒᵒ = a`,
2. contravariance `(a * b)ᵒ = bᵒ * aᵒ`
3. self-converse identity `1ᵒ = 1`
4. join-preservation `(sSup s)ᵒ = sSup (·ᵒ '' s)`
together with monotonicity of `·ᵒ`.

We take exactly **three** as primitive: involutivity, contravariance, and
monotonicity. The remaining two are *derived*:

* `1ᵒ = 1` follows from involutivity, contravariance and the monoid unit laws
  (`converse_one`);
* join-preservation follows from monotonicity and involutivity, since a monotone
  involution is an order isomorphism and thus preserves arbitrary joins
  (`converse_join_preservation`).

Monotonicity and join-preservation are equivalent given involutivity; we assume
the former and recover the latter.

## References

* K.I. Rosenthal. *Quantales and their applications.* Longman Scientific
  & Technical, 1990. (Involutive quantales and the four converse laws.)
* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.

-/
@[expose] public section

universe u

/-- An involutive quantale is a monoid whose composition distributes over
arbitrary joins in a complete lattice (`IsQuantale`), equipped with an
order-preserving contravariant involution `·ᵒ`. -/
class IsInvolutiveQuantale (α : Type u)
    [Monoid α]
    [CompleteLattice α]
    [IsQuantale α] where

  /-- The converse operation `·ᵒ`. -/
  converse : α → α

  /-- Involutivity of converse: applying converse twice is the identity. -/
  converse_involutivity (a : α) : converse (converse a) = a

  /-- Contravariance of converse over composition: swapping the endpoints of a
  composite reverses the order of the factors. -/
  converse_compositionality (a b : α) : converse (a * b) = converse b * converse a

  /-- Monotonicity of converse. Equivalent to join-preservation given
  involutivity; we take the former as primitive and derive the latter,
  see `converse_join_preservation`. -/
  converse_monotonicity {a b : α} : a ≤ b → converse a ≤ converse b

attribute [simp] IsInvolutiveQuantale.converse_involutivity

@[inherit_doc]
scoped[IsInvolutiveQuantale] postfix:max "ᵒ" => IsInvolutiveQuantale.converse

namespace IsInvolutiveQuantale
open scoped IsInvolutiveQuantale

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable {a b : α}

/-- Converse is injective. Derived from `converse_involutivity`. -/
theorem converse_injectivity : Function.Injective (converse : α → α) := fun _ _ h => by
  have := congrArg converse h
  simpa using this

/-- Converse reflects the order: `aᵒ ≤ bᵒ ↔ a ≤ b`. Derived from monotonicity
and involutivity. -/
theorem converse_monotonicity_iff : aᵒ ≤ bᵒ ↔ a ≤ b := by
  refine ⟨fun h => ?_, converse_monotonicity⟩
  have := converse_monotonicity h
  simpa using this

/-- `Δᵒ = Δ`: the identity is self-converse. Derived from the monoid unit laws
together with `converse_involutivity` and `converse_compositionality`. -/
@[simp]
theorem converse_one : (1 : α)ᵒ = 1 := by
  have key : ∀ a : α, a * (1 : α)ᵒ = a := fun a =>
    calc a * (1 : α)ᵒ
        = aᵒᵒ * (1 : α)ᵒ := by rw [converse_involutivity]
      _ = ((1 : α) * aᵒ)ᵒ := (converse_compositionality _ _).symm
      _ = aᵒᵒ := by rw [one_mul]
      _ = a := converse_involutivity a
  have h := key 1
  rwa [one_mul] at h

/-- Join-preservation of converse: `(sSup s)ᵒ = sSup (·ᵒ '' s)`. Derived from
monotonicity and involutivity (a monotone bijection with monotone inverse is an
order isomorphism, hence preserves arbitrary joins). -/
theorem converse_join_preservation (s : Set α) : (sSup s)ᵒ = sSup (converse '' s) := by
  refine le_antisymm ?_ ?_
  · have h : sSup s ≤ (sSup (converse '' s))ᵒ := by
      refine sSup_le fun a ha => ?_
      have hle : aᵒ ≤ sSup (converse '' s) := le_sSup ⟨a, ha, rfl⟩
      have := converse_monotonicity hle
      simpa using this
    have := converse_monotonicity h
    simpa using this
  · refine sSup_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact converse_monotonicity (le_sSup ha)

/-- Binary form of join-preservation. Derived. -/
@[simp]
theorem converse_join_preservation_binary (a b : α) : (a ⊔ b)ᵒ = aᵒ ⊔ bᵒ := by
  rw [← sSup_pair, converse_join_preservation, Set.image_pair, sSup_pair]

/-- The bottom element is self-converse. Derived from `converse_join_preservation`
on the empty set. -/
@[simp]
theorem converse_bot_strictness : (⊥ : α)ᵒ = ⊥ := by
  have h := converse_join_preservation (∅ : Set α)
  rwa [Set.image_empty, sSup_empty] at h

end IsInvolutiveQuantale
