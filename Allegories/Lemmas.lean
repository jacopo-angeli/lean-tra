import Allegories.Basic

/-!
# Order-theoretic lemmas for allegories

This file develops the partial order on hom-sets of an allegory induced by
the intersection operation, and proves basic order-theoretic properties of
the allegory operations.

## Main definitions

* `Allegory.hom_le` — the partial order `R ≤ₐ S` defined as `intersection R S = R`

## Main results
* `Allegory.hom_le_reflexivity`, `hom_le_transitivity`, `hom_le_antisymmetry` — `≤ₐ` is a partial order
* `Allegory.converse_monotone` — converse is monotone with respect to `≤ₐ`
* `Allegory.galois_law` — converse forms a Galois connection with itself
* `Allegory.intersection_le_left`, `intersection_le_right`, `le_intersection` — intersection is the meet

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990
-/

open CategoryTheory

attribute [simp] Allegory.converse_id
attribute [simp] Allegory.converse_involution
attribute [simp] Allegory.intersection_idempotence
attribute [simp] Allegory.intersection_associativity
attribute [simp] Allegory.converse_composition
attribute [simp] Allegory.converse_intersection

namespace Allegory

variable {A : Type*} [Allegory A] {X Y : A}

/-- `R ≤ₐ S` iff `R` is below `S` in the hom-set partial order,
defined as `intersection R S = R`. -/
def hom_le (R S : X ⟶ Y) : Prop := intersection R S = R

end Allegory

/-- Notation for the hom-set partial order on allegory morphisms. -/
scoped[Allegory] notation:50 R:51 " ≤ₐ " S:51 => Allegory.hom_le R S

namespace Allegory

open Allegory

variable {A : Type*} [Allegory A] {X Y : A}

/-- `≤ₐ` is reflexive. -/
theorem hom_le_reflexivity (R : X ⟶ Y) : R ≤ₐ R := by
  unfold hom_le at *
  exact intersection_idempotence R

/-- `≤ₐ` is transitive. -/
theorem hom_le_transitivity {R S T : X ⟶ Y} (h1 : R ≤ₐ S) (h2 : S ≤ₐ T) : R ≤ₐ T := by
  unfold hom_le at *
  rw [← h1, ← intersection_associativity, h2, h1]

/-- `≤ₐ` is antisymmetric. -/
theorem hom_le_antisymmetry {R S : X ⟶ Y} (h1 : R ≤ₐ S) (h2 : S ≤ₐ R) : R = S := by
  unfold hom_le at *
  rw [← h1, intersection_commutativity, h2]

/-- Converse is monotone with respect to `≤ₐ`. -/
theorem converse_monotone {R S : X ⟶ Y} (h : R ≤ₐ S) : converse R ≤ₐ converse S := by
  unfold hom_le at *
  rw [← converse_intersection]
  rw [h]

/-- Galois law: `R ≤ₐ converse S` iff `converse R ≤ₐ S`. -/
theorem galois_law {R : X ⟶ Y} {S : Y ⟶ X} : R ≤ₐ converse S ↔ converse R ≤ₐ S := by
  constructor
  intro h
  have h1 := converse_monotone h
  simp at h1
  exact h1
  intro h
  have h1 := converse_monotone h
  simp at h1
  exact h1

/-- Intersection is a lower bound on the left argument. -/
theorem intersection_le_left {R S : X ⟶ Y} : intersection R S ≤ₐ R := by
  unfold hom_le at *
  rw [← intersection_commutativity, intersection_associativity, intersection_idempotence]

/-- Intersection is a lower bound on the right argument. -/
theorem intersection_le_right {R S : X ⟶ Y} : intersection R S ≤ₐ S := by
  unfold hom_le at *
  rw [← intersection_associativity, intersection_idempotence]

/-- Intersection is the greatest lower bound. -/
theorem le_intersection {R S T : X ⟶ Y} (h1 : R ≤ₐ S) (h2 : R ≤ₐ T) : R ≤ₐ intersection S T := by
  unfold hom_le at *
  rw[intersection_associativity, h1, h2]

end Allegory
