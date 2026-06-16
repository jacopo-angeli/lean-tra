import Allegory.Basic
import Allegory.Distributive
import Mathlib.Order.CompletePartialOrder

/-!
# Locally Complete Allegories

A locally complete allegory (Freyd–Scedrov §2.22; Gavazzo, LICS 2026, Definition 2)
is a distributive allegory in which each hom-set `X ⟶ Y` is a complete lattice and
composition and finite intersection preserve arbitrary joins. Concretely, for any
family `(Sᵢ)` one has `R ≫ (⨆ i, Sᵢ) = ⨆ i, (R ≫ Sᵢ)`, and for the empty family
this specialises to `R ≫ ⊥ = ⊥`. These conditions express that morphisms behave
like relations closed under arbitrary unions and that relational composition is
continuous with respect to these unions. This structure is strong enough to
recover division as right adjoints to composition, and it is the precise base on
which `TRA` is built in `Allegory/TRA/Basic.lean`.

## Main definitions

* `Allegory.LocallyCompleteAllegory` — a distributive allegory with complete hom-set lattices and continuous composition / intersection
* `Allegory.LocallyCompleteAllegory.homCompleteLattice` — each hom-set `X ⟶ Y` is a `CompleteLattice`

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, §2.22
* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 2
-/

open CategoryTheory

namespace Allegory

    class LocallyCompleteAllegory (A : Type*) extends DistributiveAllegory A where

    homCompleteLattice : ∀ X Y : A, CompleteLattice (X ⟶ Y)

    comp_iSup_right : ∀ {X Y Z : A} {ι : Type*} (R : X ⟶ Y) (f : ι → (Y ⟶ Z)),
        letI := homCompleteLattice Y Z
        letI := homCompleteLattice X Z
        R ≫ ⨆ i, f i = ⨆ i, R ≫ f i
    /-- Composition distributes over arbitrary joins on the left. -/
    iSup_comp_left : ∀ {X Y Z : A} {ι : Type*} (f : ι → (X ⟶ Y)) (R : Y ⟶ Z),
        letI := homCompleteLattice X Y
        letI := homCompleteLattice X Z
        (⨆ i, f i) ≫ R = ⨆ i, f i ≫ R
    /-- Intersection distributes over arbitrary joins (§2.22). -/
    intersection_iSup : ∀ {X Y : A} {ι : Type*} (R : X ⟶ Y) (f : ι → (X ⟶ Y)),
        letI := homCompleteLattice X Y
        intersection R (⨆ i, f i) = ⨆ i, intersection R (f i)

    @[reducible]
    instance instHomCompleteLattice {A : Type*} [LocallyCompleteAllegory A] (X Y : A) : CompleteLattice (X ⟶ Y) := LocallyCompleteAllegory.homCompleteLattice X Y

end Allegory
