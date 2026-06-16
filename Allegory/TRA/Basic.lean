import Allegory.LocallyComplete
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Term Relation Algebras

A Term Relation Algebra (TRA) (Gavazzo, LICS 2026, Definition 6) is a locally
complete allegory equipped with additional structure modelling substitution,
Howe-style closure, and a cocartesian decomposition of a relator. It extends a
locally complete distributive allegory, so each hom-set is a complete lattice and
composition and intersection preserve arbitrary joins. A TRA enriches the algebra
of relations with a semantic operator `tilde` (semirelator / Howe-extension), a
coreflexive diagonal-like relation `Δη`, and a substitution operation `·[·]`
forming a closed monoid. The four defining conditions are: `tilde` is
ω-cocontinuous and strict on composition while preserving converse and order;
the equation `x = (Δη ⊔ ˜x) ; a` has a least solution `aᴴ` (Howe closure);
`(A, Δη, ·[·])` forms a closed monoid with substitution units, associativity, and
a right adjoint; and substitution distributes over the semirelator,
`˜R[b] ≤ ˜(R[b])`. The cocartesian structure decomposes `˜R` into a constant
coreflexive part and a dynamic part, `˜R = Δη ⊔ ˆR`, with orthogonality
`Δη ; ˜R ≤ ⊥`, expressing separation of variables. This file is the foundation
on which every TRA-level construction in `Allegory/TRA/*` is built.

## Main definitions

* `Allegory.TRA` — locally complete allegory with cocartesian semirelators, Howe closure, and substitution

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 6
* Freyd, Scedrov, *Categories, Allegories*, 1990
-/

open CategoryTheory

namespace Allegory

  class TRA (A : Type*) extends LocallyCompleteAllegory A where

    delta_eta : ∀ {X : A}, X ⟶ X
    delta_eta_coreflexive : ∀ {X : A}, (delta_eta : X ⟶ X) ≤ 𝟙 X
    delta_eta_symmetric : ∀ {X : A}, converse (delta_eta : X ⟶ X) ≤ delta_eta
    delta_eta_cotransitive : ∀ {X : A}, (delta_eta : X ⟶ X) ≤ delta_eta ≫ delta_eta

    tilde : ∀ {X Y : A}, (X ⟶ Y) → (X ⟶ Y)
    tilde_monotonicity : ∀ {X Y : A} {R S : X ⟶ Y}, R ≤ S → tilde R ≤ tilde S
    tilde_identity_oplax : ∀ {X : A}, tilde (𝟙 X) ≤ 𝟙 X
    tilde_composition : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z), tilde (R ≫ S) = tilde R ≫ tilde S
    tilde_converse : ∀ {X Y : A} (R : X ⟶ Y), tilde (converse R) = converse (tilde R)
    tilde_omega_cocontinuous : ∀ {X Y : A} (c : ℕ →o (X ⟶ Y)), tilde (⨆ i, c i) = ⨆ i, tilde (c i)

    cocartesian_orthogonality : ∀ {X Y : A} (R : X ⟶ Y),delta_eta ≫ tilde R ≤ ⊥

    substitution : ∀ {X Y : A}, (X ⟶ Y) → (X ⟶ X) → (X ⟶ Y)
    substitution_monotonicity_left : ∀ {X Y : A} {R S : X ⟶ Y} (T : X ⟶ X), R ≤ S → substitution R T ≤ substitution S T
    substitution_monotonicity_right : ∀ {X Y : A} (R : X ⟶ Y) {S T : X ⟶ X}, S ≤ T → substitution R S ≤ substitution R T
    substitution_identity_left_colax : ∀ {X : A} (S : X ⟶ X), substitution (𝟙 X) S ≤ 𝟙 X
    substitution_composition_left : ∀ {X Z : A} (R : X ⟶ X) (S : X ⟶ Z) (T : X ⟶ X), substitution (R ≫ S) T ≤ substitution R T ≫ substitution S T
    substitution_composition_right : ∀ {X : A} (R S T : X ⟶ X), substitution R (S ≫ T) ≤ substitution R S ≫ substitution R T
    substitution_converse_left : ∀ {X : A} (R S : X ⟶ X), substitution (converse R) S = converse (substitution R S)
    substitution_converse_right : ∀ {X : A} (R S : X ⟶ X), substitution R (converse S) = converse (substitution R S)

    substitution_omega_left : ∀ {X Y : A} (c : ℕ →o (X ⟶ Y)) (T : X ⟶ X), substitution (⨆ i, c i) T = ⨆ i, substitution (c i) T

    substitution_right_unit : ∀ {X Y : A} (R : X ⟶ Y),   substitution R delta_eta = R
    substitution_left_unit : ∀ {X : A} (S : X ⟶ X), substitution delta_eta S = S
    substitution_assoc : ∀ {X Y : A} (R : X ⟶ Y) (S T : X ⟶ X), substitution (substitution R S) T = substitution R (substitution S T)
    substitution_right_residual : ∀ {X Y : A}, (X ⟶ X) → (X ⟶ Y) → (X ⟶ Y)
    substitution_right_residual_adjunction : ∀ {X Y : A} (b : X ⟶ X) (R S : X ⟶ Y), substitution R b ≤ S ↔ R ≤ substitution_right_residual b S

    howe : ∀ {X : A}, (X ⟶ X) → (X ⟶ X)
    howe_fixed_point : ∀ {X : A} (a : X ⟶ X), howe a = (delta_eta ⊔ tilde (howe a)) ≫ a
    howe_induction : ∀ {X : A} (a x : X ⟶ X), (delta_eta ⊔ tilde x) ≫ a ≤ x → howe a ≤ x
    howe_delta : ∀ {X : A}, howe (𝟙 X) = 𝟙 X

    substitution_tilde_distrib : ∀ {X Y : A} (R : X ⟶ Y) (S : X ⟶ X), substitution (tilde R) S ≤ tilde (substitution R S)

end Allegory
