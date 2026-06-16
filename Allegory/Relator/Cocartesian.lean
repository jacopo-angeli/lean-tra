import Allegory.Relator.Basic

/-!
# Cocartesian Decomposition and Cocartesian Relator Triple

A cocartesian decomposition of a relator `F : A ⇝ A` is a pair of semirelators
`Fl`, `Fr` such that `F = Fl ∨ Fr` and `Fl ; Fr ≤ ⊥`, where `∨` is extended to
relators pointwise and `;` is relator (functor) composition
(Gavazzo, LICS 2026, Definition 5). In the multi-object categorical setting the
pointwise composition `Fl(R) ; Fr(R)` is not well-typed for general `R : X ⟶ Y`,
so the orthogonality condition is expressed as relator composition
`Fr(Fl(R)) ≤ ⊥`, which recovers the paper's condition in the one-object case.
This structure provides the formal underpinning for the cocartesian
decomposition required by a TRA in `Allegory/TRA/Basic.lean`.

## Main definitions

* `Allegory.CocartesianDecomposition` — cocartesian decomposition of a relator into two semirelators
* `Allegory.CocartesianRelatorTriple` — bundled relator together with its cocartesian decomposition

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 5
-/

open CategoryTheory

namespace Allegory

variable (A : Type*) [LocallyCompleteAllegory A]

/-- A cocartesian decomposition of a relator `F : A ⇝ A` is a pair of
semirelators `Fl`, `Fr` such that `F = Fl ∨ Fr` and `Fl ; Fr ≤ ⊥` pointwise
(Paper 2026, Definition 5). -/
structure CocartesianDecomposition (F : Relator A A) where
  /-- The left semirelator of the decomposition. -/
  left_semirelator        : Semirelator A A
  /-- The right semirelator of the decomposition. -/
  right_semirelator       : Semirelator A A
  /-- The left semirelator has the same object map as `F`. -/
  left_object_agreement   : left_semirelator.obj = F.obj
  /-- The right semirelator has the same object map as `F`. -/
  right_object_agreement  : right_semirelator.obj = F.obj
  /-- Pointwise join decomposition: `F(R) = Fl(R) ⊔ Fr(R)` for all morphisms.
      Renders `F = Fl ∨ Fr` from Definition 5. The object-map agreements transport
      `Fl(R)` and `Fr(R)` into the hom-set `F.obj X ⟶ F.obj Y`. -/
  pointwise_join          : ∀ {X Y : A} (R : X ⟶ Y),
      F.map R
        = (left_object_agreement ▸ left_semirelator.map R)
          ⊔ (right_object_agreement ▸ right_semirelator.map R)
  /-- Relator-composition orthogonality: `(Fl ; Fr)(R) ≤ ⊥` for all morphisms,
      where `;` is relator (functor) composition following the left-to-right
      convention of the paper: `Fl` is applied first, then `Fr`.
      Renders `Fl ; Fr ≤ ⊥` from Definition 5. -/
  pointwise_orthogonality : ∀ {X Y : A} (R : X ⟶ Y),
      right_semirelator.map (left_semirelator.map R) ≤ ⊥

/-- A cocartesian relator triple `(F, Fl, Fr)` bundles a relator `F` on `A`
with its cocartesian decomposition into two semirelators `Fl` and `Fr`. -/
structure CocartesianRelatorTriple where
  /-- The relator being decomposed. -/
  relator       : Relator A A
  /-- The cocartesian decomposition of the relator into two semirelators. -/
  decomposition : CocartesianDecomposition A relator

end Allegory
