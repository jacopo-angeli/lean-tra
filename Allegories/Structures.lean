import Allegories.Basic
import Allegories.Lemmas
import Mathlib.Order.CompleteLattice.Defs

/-!
# Extended allegory structures

This file defines three classes that extend `Allegory` with additional structure:
tabulations, a unit object, and locally complete hom-sets.

## Main definitions

* `TabularAllegory` — every morphism has a tabulation (Freyd–Scedrov §2.147, Ferro §3.1)
* `UnitaryAllegory` — the allegory has a unit object (Freyd–Scedrov §2.1, Ferro §3.1)
* `LocallyCompleteAllegory` — every hom-set carries a complete lattice structure
  compatible with the allegory order (Freyd–Scedrov §2.1)

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, §2.1 and §2.147
* Ferro, *Formalizzazione delle Allegorie*, Università di Padova, 2024/2025, §3.1
-/

open CategoryTheory Allegory

/-- A tabular allegory is an allegory in which every morphism `R : X ⟶ Y` admits
a *tabulation*: a span `h : E ⟶ X`, `k : E ⟶ Y` such that `R = hᵒ ≫ k` and the
two legs are jointly monic, expressed as `(h ≫ hᵒ) ∩ (k ≫ kᵒ) = 𝟙 E`. -/
class TabularAllegory (A : Type*) extends Allegory A where
  /-- Every morphism `R : X ⟶ Y` has a tabulation. -/
  protected has_tabulation : ∀ {X Y : A} (R : X ⟶ Y),
      ∃ (E : A) (h : E ⟶ X) (k : E ⟶ Y),
          R = converse h ≫ k ∧
          intersection (h ≫ converse h) (k ≫ converse k) = 𝟙 E

/-- A unitary allegory is an allegory equipped with a distinguished *unit object* whose
endomorphism hom-set has `𝟙 unit` as its greatest element under `≤ₐ`. -/
class UnitaryAllegory (A : Type*) extends Allegory A where
  /-- The unit object. -/
  unit_object : A
  /-- Every endomorphism of `unit` is below the identity. -/
  protected unit_top : ∀ (R : unit_object ⟶ unit_object), R ≤ₐ 𝟙 unit_object
  protected unit_total : ∀ (B : A), ∃ (S : B ⟶ unit_object), 𝟙 B ≤ₐ S ≫ converse S

/-- A locally complete allegory is an allegory in which each hom-set `X ⟶ Y` carries
a `CompleteLattice` structure. Concretely, this adds suprema and infima for arbitrary
families of morphisms.

Following the pattern of `Preadditive.homGroup`, the lattice structure is stored as a
field `homCompleteLattice` and registered as a typeclass instance. -/
class LocallyCompleteAllegory (A : Type*) extends Allegory A where
  /-- Each hom-set is a complete lattice. -/
  homCompleteLattice : ∀ X Y : A, CompleteLattice (X ⟶ Y)

@[reducible]
instance instHomCompleteLattice {A : Type*} [LocallyCompleteAllegory A] (X Y : A) : CompleteLattice (X ⟶ Y) := LocallyCompleteAllegory.homCompleteLattice X Y
