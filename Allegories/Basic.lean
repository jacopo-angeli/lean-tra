import Mathlib.CategoryTheory.Category.Basic

/-!
# Allegories

Defines allegories in the sense of Freyd and Scedrov, as categories equipped
with a converse operation and an intersection on hom-sets, satisfying the
modular law.

## Main definitions

* `Allegory` — a category with converse and hom-set intersection

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, Definition 2.11
-/

open CategoryTheory

/-- An allegory is a category where each hom-set carries an intersection
operation and every morphism has a converse, satisfying the modular law.
Domain and codomain constraints on `converse` and `intersection` are enforced
by their types: `converse : (X ⟶ Y) → (Y ⟶ X)` and
`intersection : (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)`. -/

class Allegory (A : Type*) extends Category A where

  converse : ∀ {X Y : A}, (X ⟶ Y) → (Y ⟶ X)
  intersection : ∀ {X Y : A}, (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)

  converse_id                 : ∀ {X : A}, converse (𝟙 X) = 𝟙 X
  converse_involution         : ∀ {X Y : A} (R : X ⟶ Y), converse (converse R) = R
  intersection_idempotence    : ∀ {X Y : A} (R : X ⟶ Y), intersection R R = R
  intersection_commutativity  : ∀ {X Y : A} (R S : X ⟶ Y), intersection R S = intersection S R
  intersection_associativity  : ∀ {X Y : A} (R S T : X ⟶ Y), intersection R (intersection S T) = intersection (intersection R S) T
  converse_composition        : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z), converse (R ≫ S) = converse S ≫ converse R
  converse_intersection       : ∀ {X Y : A} (R S : X ⟶ Y), converse (intersection R S) = intersection (converse R) (converse S)
  composition_distributivity  : ∀ {X Y Z : A} (R : X ⟶ Y) (S T : Y ⟶ Z), R ≫ intersection S T = intersection (intersection (R ≫ S) (R ≫ intersection S T)) (R ≫ T)
  modular_law                 : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z) (T : X ⟶ Z), intersection (R ≫ S) T = intersection (intersection (R ≫ S) T) (intersection R (T ≫ converse S) ≫ S)

