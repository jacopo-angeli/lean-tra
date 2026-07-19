/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Quantale

/-!
# Involutive quantales

Algebraic base for a Lean formalisation of Gavazzo's Term Relation Algebras
(TRAs). Gavazzo presents the base algebra of relations as a *locally complete
allegory*. We instead work with the equivalent — in the one-object case —
notion of a *unital involutive quantale*, since this is the presentation that
rests directly on Mathlib's `IsQuantale`, avoiding the categorical overhead of
allegories while capturing the same algebra of relations.

Mathlib's `IsQuantale` is a mixin over a semigroup and a complete lattice which
does not fix a unit and does not carry an involution. We enrich it by working
over `Monoid` and introducing a single new datum, the converse operation `·ᵒ`.

## Axioms vs. derived laws

The involution is governed by four laws — involutivity `aᵒᵒ = a`, contravariance
`(a * b)ᵒ = bᵒ * aᵒ`, self-converse identity `1ᵒ = 1`, and join-preservation
`(sSup s)ᵒ = sSup (·ᵒ '' s)` — together with monotonicity of `·ᵒ`.

We take exactly **three** as primitive: involutivity, contravariance, and
monotonicity. The remaining two are *derived*:

* `1ᵒ = 1` follows from involutivity, contravariance and the monoid unit laws
  (`converse_one`);
* join-preservation follows from monotonicity and involutivity, since a monotone
  involution is an order isomorphism and thus preserves arbitrary joins
  (`converse_sSup`).

Monotonicity and join-preservation are equivalent given involutivity; we assume
the former and recover the latter.

## Main definitions

* `IsInvolutiveQuantale` — the mixin typeclass, adding `·ᵒ` and its three
  primitive laws over `Monoid` + `CompleteLattice` + `IsQuantale`.

## Main results

* `IsInvolutiveQuantale.converse_one` — the self-converse identity `1ᵒ = 1`,
  derived.
* `IsInvolutiveQuantale.converse_le_converse_iff` — `·ᵒ` is an order embedding.
* `IsInvolutiveQuantale.converse_sSup`, `converse_iSup`, `converse_sup`,
  `converse_bot` — join-preservation of `·ᵒ` and its consequences, derived.

## Notation

* `aᵒ` for `IsInvolutiveQuantale.converse a`, scoped to `IsInvolutiveQuantale`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. (Base algebra presented there as a locally complete allegory;
  the involutive-quantale presentation used here is equivalent in the
  one-object case.)
-/
@[expose] public section

universe u

/-- An involutive quantale is a monoid whose composition distributes over
arbitrary joins in a complete lattice (`IsQuantale`), equipped with an
order-preserving contravariant involution `·ᵒ`.

The one-object case of the base algebra of the paper cited in the module
`References` block, presented there over allegories. Only three of the four
involution laws are taken as primitive here: `Δᵒ = Δ` and join-preservation
are `converse_one` and `converse_sSup` below, both derived. -/
class IsInvolutiveQuantale (α : Type u)
    [Monoid α] [CompleteLattice α] [IsQuantale α] where
  /-- The converse operation `·ᵒ`. -/
  converse : α → α
  /-- Involutivity of converse: applying converse twice is the identity. -/
  protected converse_converse (a : α) : converse (converse a) = a
  /-- Contravariance of converse over composition: swapping the endpoints of a
  composite reverses the order of the factors. -/
  protected converse_mul (a b : α) : converse (a * b) = converse b * converse a
  /-- Monotonicity of converse. The source lists join-preservation among the
  axioms instead; the two are equivalent given involutivity, see
  `converse_sSup`. -/
  protected converse_mono ⦃a b : α⦄ : a ≤ b → converse a ≤ converse b

@[inherit_doc]
scoped[IsInvolutiveQuantale]
  postfix:max "ᵒ" => IsInvolutiveQuantale.converse

namespace IsInvolutiveQuantale

open scoped IsInvolutiveQuantale

variable {α : Type u} {ι : Sort*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable {a b : α} {s : Set α} {f : ι → α}

/-- Involutivity of converse, restated with notation. -/
@[simp]
theorem converse_involutive (a : α) : aᵒᵒ = a :=
  IsInvolutiveQuantale.converse_converse a

/-- Contravariance of converse over composition, restated with notation. -/
theorem mul_converse (a b : α) : (a * b)ᵒ = bᵒ * aᵒ :=
  IsInvolutiveQuantale.converse_mul a b

/-- Monotonicity of converse, restated with notation. -/
theorem converse_le_converse (h : a ≤ b) : aᵒ ≤ bᵒ :=
  IsInvolutiveQuantale.converse_mono h

/-- Converse is injective. Derived from `converse_involutive`. -/
theorem converse_injective : Function.Injective (converse : α → α) := fun _ _ h => by
  have := congrArg converse h
  simpa using this

/-- Converse reflects the order: `aᵒ ≤ bᵒ ↔ a ≤ b`. Derived from monotonicity
and involutivity. -/
theorem converse_le_converse_iff : aᵒ ≤ bᵒ ↔ a ≤ b := by
  refine ⟨fun h => ?_, converse_le_converse⟩
  have := converse_le_converse h
  simpa using this

/-- `Δᵒ = Δ`: the identity is self-converse. Derived from the monoid unit laws
together with `converse_involutive` and `mul_converse`; see the module
docstring for the argument. Not an axiom here, although the source lists it as
one. -/
@[simp]
theorem converse_one : (1 : α)ᵒ = 1 := by
  have key : ∀ a : α, a * (1 : α)ᵒ = a := fun a =>
    calc a * (1 : α)ᵒ
        = aᵒᵒ * (1 : α)ᵒ := by rw [converse_involutive]
      _ = ((1 : α) * aᵒ)ᵒ := (mul_converse _ _).symm
      _ = aᵒᵒ := by rw [one_mul]
      _ = a := converse_involutive a
  have h := key 1
  rwa [one_mul] at h

/-- Join-preservation of converse: `(sSup s)ᵒ = sSup (·ᵒ '' s)`. Derived from
monotonicity and involutivity (a monotone bijection with monotone inverse is an
order isomorphism, hence preserves arbitrary joins). Not an axiom here, although
the source lists it as one. -/
theorem converse_sSup (s : Set α) : (sSup s)ᵒ = sSup (converse '' s) := by
  refine le_antisymm ?_ ?_
  · have h : sSup s ≤ (sSup (converse '' s))ᵒ := by
      refine sSup_le fun a ha => ?_
      have hle : aᵒ ≤ sSup (converse '' s) := le_sSup ⟨a, ha, rfl⟩
      have := converse_le_converse hle
      simpa using this
    have := converse_le_converse h
    simpa using this
  · refine sSup_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact converse_le_converse (le_sSup ha)

/-- Indexed form of `converse_sSup`. Derived. -/
theorem converse_iSup (f : ι → α) : (⨆ i, f i)ᵒ = ⨆ i, (f i)ᵒ := by
  rw [iSup, converse_sSup, ← Set.range_comp, iSup]
  rfl

/-- Binary form of join-preservation. Derived. -/
@[simp]
theorem converse_sup (a b : α) : (a ⊔ b)ᵒ = aᵒ ⊔ bᵒ := by
  rw [← sSup_pair, converse_sSup, Set.image_pair, sSup_pair]

/-- The bottom element is self-converse. Derived from `converse_sSup` on the
empty set. -/
@[simp]
theorem converse_bot : (⊥ : α)ᵒ = ⊥ := by
  have h := converse_sSup (∅ : Set α)
  rwa [Set.image_empty, sSup_empty] at h

end IsInvolutiveQuantale
