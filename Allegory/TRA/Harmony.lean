import Allegory.TRA.Properties

-- ! Incorporare in Congruence.lean

/-!

# Harmony Axiom

The Harmony Axiom expresses a fundamental compatibility between operational
decomposition and substitution in a Term Relation Algebra. It states that for
any compatible relation `b`, the interaction between the destructor bracket
`⟨·,·⟩`, the Howe-extension component `˜·`, and substitution is controlled by
the inequality `⟨â, a⟩ ; b ≤ b ; a[a]`. This can be read as a parametricity
principle for computation: the behaviour of `b` is determined entirely by its
outer structure and its substitution instances. Harmony is consumed by the
congruence side of the Bridge Theorem (S3, Lemma 34) to turn parametricity into
a substitutivity statement about the op-Howe extension.

## Main definitions

* `Allegory.TRA.Harmony` — typeclass packaging the destructor bracket and the harmony inequality

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026
-/

open CategoryTheory

namespace Allegory.TRA

    variable {A : Type*} [TRA A]

    class Harmony (A : Type*) [TRA A] where
        bracket : ∀ {X : A}, (X ⟶ X) → (X ⟶ X) → (X ⟶ X)
        harmony : ∀ {X : A} (a b : X ⟶ X), Compatible b → bracket (tilde a) a ≫ b ≤ b ≫ substitution a b

end Allegory.TRA
