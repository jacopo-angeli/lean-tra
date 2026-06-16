import Allegory.LocallyComplete
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Relators

Defines a hierarchy of structure-preserving maps between locally complete
allegories, ordered by strength of what they preserve on composition:
`ColaxRelator A B ← Semirelator A B ← Relator A B`. Each layer adds a strictness
axiom: a colax relator becomes a semirelator by being strict on composition, and
a semirelator becomes a relator by being strict on identity. In the one-object
(monoid) view of an allegory, these are the relational counterparts of functors,
capturing how syntactic operations on term algebras act on relation-algebraic
structure. Separately, ω-cocontinuity — preservation of joins of monotone
ω-chains — is exposed as a propositional mixin `OmegaCocontinuous F` over a
semirelator `F`, since Condition 1 of Definition 6 in Gavazzo only requires the
semirelator `˜·` to be ω-cocontinuous, never asking it to be strict on identity.
By structure inheritance the same instance attaches uniformly to a `Relator`.

## Main definitions

* `Allegory.ColaxRelator` — monotone, colax on identity and composition, preserves converse
* `Allegory.Semirelator` — colax relator that is strict on composition
* `Allegory.Relator` — semirelator that is strict on identity
* `Allegory.OmegaCocontinuous` — propositional class asserting preservation of joins of monotone ω-chains

## References

* Kawahara, Y., *Notes on the Universality of Relational Functors*, 1973
* Bird, R., de Moor, O., *Algebra of Programming*, Prentice Hall, 1997
* Backhouse, R. et al., *Polynomial Relators*, AMAST, 1991
* Backhouse, R., Hoogendijk, P., *Elements of a Relational Theory of Datatypes*, 1993
* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 6
-/

open CategoryTheory

namespace Allegory

variable (A B : Type*) [LocallyCompleteAllegory A] [LocallyCompleteAllegory B]


/-- A colax relator between locally complete allegories `A` and `B` is a
prefunctor that is monotone, colax on identity and composition, and preserves
converse. -/
structure ColaxRelator extends Prefunctor A B where
  /-- Monotonicity: `R ≤ S` implies `F(R) ≤ F(S)`. -/
  morphism_order_preservation     : ∀ {X Y : A} {R S : X ⟶ Y}, R ≤ S → map R ≤ map S
  /-- Colax on identity: the image of the identity is below the identity. -/
  identity_colax                  : ∀ (X : A), map (𝟙 X) ≤ 𝟙 (obj X)
  /-- Colax on composition: the image of a composite is below the composite
      of the images. -/
  composition_colax               : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z), map (R ≫ S) ≤ map R ≫ map S
  /-- Converse preservation: the image of the converse equals the converse
      of the image. -/
  converse_preservation           : ∀ {X Y : A} (R : X ⟶ Y), map (converse R) = converse (map R)


/-- A semirelator between locally complete allegories `A` and `B` is a colax
relator that is additionally strict on composition. -/
structure Semirelator extends ColaxRelator A B where
  /-- Strict composition preservation: the image of a composite equals the
      composite of the images. -/
  composition_strict_preservation : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z), map (R ≫ S) = map R ≫ map S


/-- A relator between locally complete allegories `A` and `B` is a semirelator
that is additionally strict on identity. This coincides with a monotone functor
preserving converse in the sense of Kawahara 1973 and Bird–de Moor 1997. -/
structure Relator extends Semirelator A B where
  /-- Strict identity preservation: the image of the identity equals the
      identity. -/
  identity_strict_preservation    : ∀ (X : A), map (𝟙 X) = 𝟙 (obj X)


-- Make the type parameters implicit for the propositional mixin below so the
-- class can be written as `OmegaCocontinuous F` with `A B` inferred from `F`.
variable {A B}

/-- A semirelator `F : Semirelator A B` is **ω-cocontinuous** when its action on
each hom-set preserves joins of monotone ω-chains.

This is a *propositional* class (`Prop`-valued mixin): rather than a separate
layer in the relator hierarchy, ω-cocontinuity is attached as an extra property
of an already-given semirelator. The carrier is `Semirelator A B` because
ω-cocontinuity is independent of identity-strictness — Definition 6 of
Paper 2026 (Condition 1) asks `˜·` to be an ω-cocontinuous *semirelator*,
not a relator. By the structure-inheritance chain `Relator A B → Semirelator A B`,
any `Relator` whose underlying `Semirelator` carries this instance is itself
ω-cocontinuous. -/
class OmegaCocontinuous (F : Semirelator A B) : Prop where
  /-- ω-chain join preservation: the image of the supremum of a monotone
      ω-chain equals the supremum of the images. -/
  omega_chain_join_preservation :
    ∀ {X Y : A} (c : ℕ →o (X ⟶ Y)), F.map (⨆ i, c i) = ⨆ i, F.map (c i)

end Allegory
