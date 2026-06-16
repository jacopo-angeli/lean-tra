import Allegory.Basic

/-!
# Distributive Allegories

A distributive allegory (Freyd–Scedrov §2.21) is an allegory equipped with a zero
morphism `0` and a binary union `∪` on each hom-set. The axioms make each hom-set
a distributive lattice (with `∩` as meet and `∪` as join) and require composition
to distribute over binary union on both sides. The redundant axioms
`union_composition`, `zero_composition`, `converse_union`, and `converse_zero`
are listed in Freyd–Scedrov §2.211 as consequences of the primary axioms but are
kept as fields because they are used constantly in proofs. This layer is the
finite-join refinement of `Allegory` and the immediate substrate for
`LocallyCompleteAllegory` and `TRA`.

## Main definitions

* `Allegory.DistributiveAllegory` — an allegory with zero morphisms and binary unions on hom-sets

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, §2.21–2.22
-/

open CategoryTheory

namespace Allegory

  class DistributiveAllegory (A : Type*) extends Allegory A where
    zero  : ∀ {X Y : A}, X ⟶ Y
    union : ∀ {X Y : A}, (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)

    union_idempotence             : ∀ {X Y : A} (R : X ⟶ Y), union R R = R
    union_commutativity           : ∀ {X Y : A} (R S : X ⟶ Y), union R S = union S R
    union_associativity           : ∀ {X Y : A} (R S T : X ⟶ Y), union R (union S T) = union (union R S) T

    zero_union                    : ∀ {X Y : A} (R : X ⟶ Y), union zero R = R

    union_intersection_absorption : ∀ {X Y : A} (R S : X ⟶ Y), union R (intersection R S) = R
    intersection_union_absorption : ∀ {X Y : A} (R S : X ⟶ Y), intersection R (union R S) = R

    intersection_union            : ∀ {X Y : A} (R S T : X ⟶ Y), intersection R (union S T) = union (intersection R S) (intersection R T)

    composition_zero                     : ∀ {X Y Z : A} (R : X ⟶ Y), R ≫ (zero : Y ⟶ Z) = zero
    composition_union                    : ∀ {X Y Z : A} (R : X ⟶ Y) (S T : Y ⟶ Z), R ≫ union S T = union (R ≫ S) (R ≫ T)

    zero_composition                     : ∀ {X Y Z : A} (R : Y ⟶ Z), (zero : X ⟶ Y) ≫ R = zero
    union_composition                    : ∀ {X Y Z : A} (R S : X ⟶ Y) (T : Y ⟶ Z), union R S ≫ T = union (R ≫ T) (S ≫ T)
    converse_union                : ∀ {X Y : A} (R S : X ⟶ Y), converse (union R S) = union (converse R) (converse S)
    converse_zero                 : ∀ {X Y : A}, converse (zero : X ⟶ Y) = (zero : Y ⟶ X)

end Allegory
