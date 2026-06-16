import Mathlib.CategoryTheory.Category.Basic

/-!
# Allegories

An allegory (Freyd–Scedrov §2.11) is a category equipped with a converse operation
`ᵒ` and a meet operation `∩` on each hom-set. The converse is an involutive
contravariant operation preserving meets. Each hom-set carries the structure of a
meet-semilattice, composition is monotone with respect to the induced order, and
composition, converse, and meet satisfy the modular law. These axioms abstract the
calculus of binary relations, where converse is relational reversal and meet is
relational intersection. This file fixes the base notion on which every other
allegory layer in this development is built — distributive, locally-complete, and
Term Relation Algebras all extend `Allegory` further down the hierarchy.

## Main definitions

* `Allegory` — a category with converse and hom-set intersection

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, §2.11
-/

open CategoryTheory

class Allegory (A : Type*) extends Category A where
  converse : ∀ {X Y : A}, (X ⟶ Y) → (Y ⟶ X)
  intersection : ∀ {X Y : A}, (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)

  converse_involution         : ∀ {X Y : A} (R : X ⟶ Y), converse (converse R) = R
  converse_composition        : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z), converse (R ≫ S) = converse S ≫ converse R
  converse_identity           : ∀ {X : A}, converse (𝟙 X) = 𝟙 X

  intersection_idempotence    : ∀ {X Y : A} (R : X ⟶ Y), intersection R R = R
  intersection_commutativity  : ∀ {X Y : A} (R S : X ⟶ Y), intersection R S = intersection S R
  intersection_associativity  : ∀ {X Y : A} (R S T : X ⟶ Y), intersection R (intersection S T) = intersection (intersection R S) T

  converse_intersection       : ∀ {X Y : A} (R S : X ⟶ Y), converse (intersection R S) = intersection (converse R) (converse S)

  composition_distributivity  : ∀ {X Y Z : A} (R : X ⟶ Y) (S T : Y ⟶ Z), R ≫ intersection S T = intersection (intersection (R ≫ S) (R ≫ intersection S T)) (R ≫ T)

  modular_law                 : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z) (T : X ⟶ Z), intersection (R ≫ S) T = intersection (intersection (R ≫ S) T) (intersection R (T ≫ converse S) ≫ S)
