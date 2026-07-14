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
