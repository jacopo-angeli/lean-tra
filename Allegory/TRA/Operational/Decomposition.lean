import Allegory.TRA.Modalities

/-!
# O1 — Operational Decomposition

An operational decomposition in a TRA refines the strict compatible structure
`˜·` into two interacting components: a constructor semirelator (introduction
forms) and a destructor bracket `⟨·, ·⟩` (elimination forms)
(Gavazzo, LICS 2026, Definition 23). These components form a cocartesian
decomposition of `˜`, meaning that the strict refinement splits into a join of
introduction and elimination behaviour. This separation captures the distinction
between value formation and elimination contexts in a purely relational
setting. The decomposition is required to be compatible with monotone
semirelator structure, the substitution action, and the S4 modality `□`. The
value coreflexive is defined as `Δκ ≜ □Δ`, identifying canonical values as
modal fixed points of identity. This file supplies the structural vocabulary
used by every operational and evaluation file in `Allegory/TRA/{Operational,Evaluation}/*`.

## Main definitions

* `Allegory.TRA.OperationalDecomposition` — typeclass packaging constructor / destructor semirelators
* `Allegory.TRA.delta_kappa` — value coreflexive `Δκ ≜ □Δ`
* `Allegory.TRA.bracketSingle` — single-position destructor `⟨a⟩ ≜ ⟨a, Δ⟩`

## Main results

* `Allegory.TRA.delta_kappa_coreflexive` — `Δκ ≤ 𝟙`
* `Allegory.TRA.delta_kappa_closed` — `Δκ` is closed

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 23
-/

open CategoryTheory

namespace Allegory.TRA

    variable {A : Type*} [TRA A]

    class OperationalDecomposition (A : Type*) [TRA A] where
    /-- Constructor semirelator `·` (introduction forms; Def. 23). -/
        constructorRel : ∀ {X : A}, (X ⟶ X) → (X ⟶ X)

    /-- Destructor bracket `⟨·, ·⟩` (elimination forms with major/minor
        positions; Def. 23). -/
        bracketRel : ∀ {X : A}, (X ⟶ X) → (X ⟶ X) → (X ⟶ X)

    -- ! maybe it's worth to bring back the semirelator hierarchy structure back
    -- ! adapted as endofunctors and endorelators

    /-- `constructorRel` is monotone (semirelator axiom, Def. 4 + Def. 23). -/
        constructorRel_monotonicity : ∀ {X : A} {R S : X ⟶ X}, R ≤ S → constructorRel R ≤ constructorRel S

    /-- `bracketRel` is monotone in the major argument (Def. 23). -/
        bracketRel_monotonicity_left : ∀ {X : A} {R S : X ⟶ X} (T : X ⟶ X), R ≤ S → bracketRel R T ≤ bracketRel S T

    /-- `bracketRel` is monotone in the minor argument (Def. 23). -/
        bracketRel_monotonicity_right : ∀ {X : A} (R : X ⟶ X) {S T : X ⟶ X}, S ≤ T → bracketRel R S ≤ bracketRel R T

    /-- **Cocartesian decomposition** `˜R = constructorRel R ⊔ bracketRel R Δ`
        (Def. 23: `˜·` is the join of the constructor and destructor at Δ). -/
        tilde_decomposition : ∀ {X : A} (R : X ⟶ X), tilde R = constructorRel R ⊔ bracketRel R (𝟙 X)

    /-- **Constructor/destructor orthogonality** (Def. 23: `·;⟨b,c⟩ ≤ ⊥`):
        introduction and elimination forms are disjoint. -/
        decomposition_orthogonality : ∀ {X : A} (R S T : X ⟶ X), constructorRel R ≫ bracketRel S T ≤ ⊥

    /-- **Substitution distributes over `constructorRel`** (Def. 23). -/
        constructorRel_substitution_distrib : ∀ {X : A} (R S : X ⟶ X), substitution (constructorRel R) S = constructorRel (substitution R S)

    /-- **Substitution distributes over `bracketRel`** (Def. 23): substitution
        passes through both positions of the destructor. -/
        bracketRel_substitution_distrib : ∀ {X : A} (R S T : X ⟶ X), substitution (bracketRel R T) S = bracketRel (substitution R S) (substitution T S)

    /-- **`□` distributes over `⟨·, b⟩`** (Def. 23: `□⟨R, b⟩ = ⟨□R, b⟩`):
        closedness of an elimination form is determined by its major argument. -/
        box_bracketRel_distrib : ∀ {X : A} (R b : X ⟶ X), box (bracketRel R b) = bracketRel (box R) b

    /-- **Value coreflexive** `Δκ ≜ □Δ` (Paper 2026, Def. 23): identifies
    canonical (value) forms as closed identities. -/
    def delta_kappa {X : A} : X ⟶ X := box (𝟙 X)

    /-- **`⟨a⟩ ≜ ⟨a, Δ⟩`** — destructor of `a`-related major arguments with
    identity minors (Paper 2026, Sec. 5; abbreviation used by O2/O3). -/
    def bracketSingle [OperationalDecomposition A] {X : A} (a : X ⟶ X) : X ⟶ X := OperationalDecomposition.bracketRel a (𝟙 X)

    /-- **`Δκ` is coreflexive**: `Δκ ≤ 𝟙` (direct from `box_le_self`). -/
    theorem delta_kappa_coreflexive {X : A} : (delta_kappa : X ⟶ X) ≤ 𝟙 X :=
      box_le_self (𝟙 X)

    /-- **`Δκ` is closed**: `Δκ ≤ □Δκ` (direct from `closed_box` applied to `𝟙`). -/
    theorem delta_kappa_closed {X : A} : Closed (delta_kappa : X ⟶ X) :=
      closed_box (𝟙 X)

end Allegory.TRA
