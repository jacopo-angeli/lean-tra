import Allegories.Basic
import Allegories.Lemmas
import Allegories.Structures
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Relators between allegories

A *relator* is a functor between allegories that preserves the allegory structure:
converse and the hom-set order `≤ₐ`. This file defines the bundled type `Allegory.Relator A B`,
following the pattern of `Adjunction` in Mathlib.

## Main definitions

* `Allegory.Relator A B` — a functor `A ⥤ B` equipped with proofs of `map_converse` and `map_monotone`
* `Allegory.Relator.id` — the identity functor on an allegory is a relator
* `Allegory.Relator.comp` — composition of relators is a relator

## References

* Freyd, Scedrov, *Categories, Allegories*, 1990, §2.1
* Ferro, *Formalizzazione delle Allegorie*, Università di Padova, 2024/2025, §3.2,
  Definition 3.2.1
-/

open CategoryTheory Allegory

namespace Allegory

/-- A relator between allegories `A` and `B` is a functor `A ⥤ B` that commutes with
converse and is monotone with respect to the hom-set order `≤ₐ`.

This bundles the underlying functor together with the structure-preservation proofs,
following the pattern of `Adjunction`. -/
structure Relator (A B : Type*) [Allegory A] [Allegory B] extends A ⥤ B where
  /-- A relator commutes with converse: `Γ(Rᵒ) = (ΓR)ᵒ`. -/
  protected map_converse : ∀ {X Y : A} (R : X ⟶ Y),
      toFunctor.map (converse R) = converse (toFunctor.map R)
  /-- A relator is monotone: `R ≤ₐ S → ΓR ≤ₐ ΓS`. -/
  protected map_monotone : ∀ {X Y : A} {R S : X ⟶ Y},
      R ≤ₐ S → toFunctor.map R ≤ₐ toFunctor.map S

namespace Relator

variable {A B C : Type*} [Allegory A] [Allegory B] [Allegory C]

/-- The identity functor on an allegory is a relator. -/
def id (A : Type*) [Allegory A] : Relator A A where
  toFunctor    := 𝟭 A
  map_converse R := by simp
  map_monotone h := by simp; exact h

/-- The composition of two relators is a relator. -/
def comp (F : Relator A B) (G : Relator B C) : Relator A C where
  toFunctor    := F.toFunctor ⋙ G.toFunctor
  map_converse R := by simp; rw [F.map_converse, G.map_converse]
  map_monotone h := G.map_monotone (F.map_monotone h)

/-- A relator preserves `≤ₐ` (explicit form of `map_monotone`). -/
theorem map_hom_le (F : Relator A B) {X Y : A} {R S : X ⟶ Y} (h : R ≤ₐ S) :
    F.map R ≤ₐ F.map S :=
  F.map_monotone h

end Relator

end Allegory
