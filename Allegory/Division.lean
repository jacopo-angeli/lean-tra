import Allegory.Distributive

/-!
# Division Allegories

A division allegory (Freyd–Scedrov §2.31) is a distributive allegory equipped with
a right-division operation `R/S` (written `rdiv R S`) for morphisms `R : X ⟶ Z`
and `S : Y ⟶ Z` sharing the same codomain. Right division is the largest morphism
`T : X ⟶ Y` such that `T ; S ≤ R`, axiomatised by counit, unit, and intersection
preservation, jointly equivalent to the Galois adjunction
`T ≤ R/S ↔ T ; S ≤ R`. Left division `S\R` is obtained by dualising via converse
and applies when `S` and `R` share the same domain. Division allegories are the
classical setting where residuals are first-class operations on relations; they
sit between `DistributiveAllegory` and `LocallyCompleteAllegory` in this
development.

## Main definitions

* `Allegory.DivisionAllegory` — a distributive allegory with right-division residuals
* `Allegory.DivisionAllegory.ldiv` — left division derived from right division by converse

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, §2.31–2.312
-/

open CategoryTheory

namespace Allegory

    class DivisionAllegory (A : Type*) extends DistributiveAllegory A where
    rdiv : ∀ {X Y Z : A}, (X ⟶ Z) → (Y ⟶ Z) → (X ⟶ Y)
    rdiv_counit : ∀ {X Y Z : A} (R : X ⟶ Z) (S : Y ⟶ Z), intersection ((rdiv R S) ≫ S) R = (rdiv R S) ≫ S
    rdiv_unit : ∀ {X Y Z : A} (T : X ⟶ Y) (S : Y ⟶ Z), intersection T (rdiv (T ≫ S) S) = T
    rdiv_intersection : ∀ {X Y Z : A} (R₁ R₂ : X ⟶ Z) (S : Y ⟶ Z), intersection (rdiv (intersection R₁ R₂) S) (intersection (rdiv R₁ S) (rdiv R₂ S)) = rdiv (intersection R₁ R₂) S

    namespace DivisionAllegory

        def ldiv {A : Type*} [DivisionAllegory A] {X Y Z : A} (S : X ⟶ Y) (R : X ⟶ Z) : Y ⟶ Z := converse (rdiv (converse R) (converse S))

    end DivisionAllegory

end Allegory
