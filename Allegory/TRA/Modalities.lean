import Allegory.TRA.Basic

/-!
# Modalities □, ♦ and Open Extension ♢

A Term Relation Algebra carries three fundamental modalities (Gavazzo,
LICS 2026, §3.2.1) that arise from interpreting relations on open vs closed
terms inside a locally complete allegory. The modalities are defined purely
from substitution and residual structure: `□a ≜ a[⊥]` closes a relation to
complete terms, `♦a ≜ a » ⊥` is the right adjoint modality in the open-extension
direction, and `♢a ≜ Δ » ♦a` is the open extension (Lassen-style lifting to
open terms). They form an instance of axiomatic cohesion (Lawvere 2007), where
an adjoint triple `ι ⊣ ♭ ⊣ ♯` induces a comonad/monad pair on relations.
Intuitively `□` forgets openness (forces completeness), `♦` introduces maximal
openness compatible with a relation, and `♢` re-embeds open semantics back into
the full algebra. This file supplies the modal vocabulary used by the
operational and similarity layers.

## Main definitions

* `Allegory.TRA.box` — closing modality `□a ≜ a[⊥]`
* `Allegory.TRA.diamond` — right adjoint modality `♦a ≜ a » ⊥`
* `Allegory.TRA.openExt` — open extension `♢a ≜ Δ » ♦a`
* `Allegory.TRA.Closed` — `a ≤ □a` characterising closed relations

## Main results

* `Allegory.TRA.box_monotonicity` — `□` is monotone
* `Allegory.TRA.box_le_self` — S4 counit law `□a ≤ a`
* `Allegory.TRA.box_composition` — `□(a ≫ b) = □a ≫ □b`
* `Allegory.TRA.box_converse` — `□` distributes over converse
* `Allegory.TRA.box_delta_eta` — `□Δη = ⊥`
* `Allegory.TRA.substitution_bot_left` — `⊥[b] ≤ ⊥`
* `Allegory.TRA.box_substitution_invariant` — `(□a)[b] ≤ □a`
* `Allegory.TRA.box_idempotent` — `□(□a) = □a`
* `Allegory.TRA.box_delta_idempotent` — `□Δ ; □Δ ≤ □Δ`
* `Allegory.TRA.box_diamond_adjunction` — cohesion adjunction `□ ⊣ ♦`
* `Allegory.TRA.closed_box` — every `□a` is closed
* `Allegory.TRA.closed_iff_eq_box` — closedness ⟺ `a = □a`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, §3.2.1
* Lawvere, *Axiomatic cohesion*, 2007
-/

open CategoryTheory

namespace Allegory.TRA

  variable {A : Type*} [TRA A]

  def box {X : A} (a : X ⟶ X) : X ⟶ X := substitution a ⊥

  def diamond {X : A} (a : X ⟶ X) : X ⟶ X :=  substitution_right_residual a ⊥

  def openExt {X : A} (a : X ⟶ X) : X ⟶ X := substitution_right_residual (𝟙 X) (diamond a)

  def Closed {X : A} (a : X ⟶ X) : Prop := a ≤ box a

  /-- **`□` is monotone** (Paper 2026, p. 76:16: "□ is monotone"). -/
  theorem box_monotonicity {X : A} {a b : X ⟶ X} (_h : a ≤ b) :
    box a ≤ box b := by
      -- deps: Allegory.TRA.substitution_monotonicity_left
      sorry

  /-- **S4 counit law `□a ≤ a`** (Paper 2026, p. 76:16: "□φ ⊆ φ"). -/
  theorem box_le_self {X : A} (a : X ⟶ X) :
    box a ≤ a := by
      show substitution a ⊥ ≤ a
      calc substitution a ⊥
          ≤ substitution a delta_eta := substitution_monotonicity_right a bot_le
        _ = a := substitution_right_unit a

  /-- **S4 multiplicative law `□(a ; b) = □a ; □b`**
  (Paper 2026, p. 76:16: "□(φ; ψ) = □φ ; □ψ"). -/
  theorem box_composition {X : A} (a b : X ⟶ X) :
    box (a ≫ b) = box a ≫ box b := by
      -- deps: Allegory.TRA.substitution_composition_left
      sorry

  /-- **`□` distributes over converse** (Paper 2026, p. 76:16: "It also
  distributes over relation converse and composition"). -/
  theorem box_converse {X : A} (a : X ⟶ X) :
    box (converse a) = converse (box a) := by
      -- deps: Allegory.TRA.substitution_converse_left
      sorry

  /-- **`□Δη = ⊥`** — no variable is a complete term
  (Paper 2026, p. 76:16: "□Δη = ⊥"). -/
  theorem box_delta_eta {X : A} :
    box (delta_eta : X ⟶ X) = ⊥ := by
      -- deps: Allegory.TRA.substitution_left_unit
      sorry

  /-- **`substitution ⊥ b ≤ ⊥`** — helper: substitution by anything in the
  second argument annihilates a bottom first argument. -/
  theorem substitution_bot_left {X Y : A} (b : X ⟶ X) :
    (substitution ⊥ b : X ⟶ Y) ≤ ⊥ := by
      -- deps: Allegory.TRA.substitution_right_residual_adjunction, bot_le
      sorry

  /-- **`(□a)[b] ≤ □a`** — substitution has no effect on complete relations
  (Paper 2026, p. 76:16: "(□φ)[ψ] ⊆ □φ"). -/
  theorem box_substitution_invariant {X : A} (a b : X ⟶ X) :
    substitution (box a) b ≤ box a := by
      -- deps: Allegory.TRA.substitution_assoc, Allegory.TRA.substitution_monotonicity_right, substitution_bot_left
      sorry

  /-- **`□` is idempotent**: `□(□a) = □a`. Standard S4-comonad law: every
  image of `□` is a fixed point of `□` (Paper 2026, p. 76:16: "□ being a
  comonad"). -/
  theorem box_idempotent {X : A} (a : X ⟶ X) :
    box (box a) = box a := by
      -- deps: Allegory.TRA.substitution_assoc, Allegory.TRA.substitution_monotonicity_right, substitution_bot_left, bot_le, le_antisymm
      sorry

  /-- **`□Δ ; □Δ ≤ □Δ`** — idempotence of the box of the identity
  (Paper 2026, p. 76:16: "□Δ ; □Δ ⊆ □Δ"). -/
  theorem box_delta_idempotent {X : A} :
    box (𝟙 X) ≫ box (𝟙 X) ≤ box (𝟙 X) := by
      -- deps: box_composition, CategoryTheory.Category.comp_id
      sorry

  /-- **Cohesion adjunction** `□ ⊣ ♦`: `□a ≤ b ↔ a ≤ ♦b`
  (Paper 2026, p. 76:16: "the (co)monadic modalities □ and ♦ on A form an
  adjunction □ ⊣ ♦ themselves"). -/
  theorem box_diamond_adjunction {X : A} (a b : X ⟶ X) :
    box a ≤ b ↔ a ≤ diamond b := by
      -- deps: Allegory.TRA.substitution_right_residual_adjunction, ι ⊣ ♭ ⊣ ♯
      sorry

  /-- **Every box is closed**: `□a` itself is a closed relation
  (standard comonad fact: the counit `box_le_self` produces a fixed point). -/
  theorem closed_box {X : A} (a : X ⟶ X) :
    Closed (box a) := by
      show box a ≤ box (box a)
      show substitution a ⊥ ≤ substitution (substitution a ⊥) ⊥
      rw [substitution_assoc]
      exact substitution_monotonicity_right a bot_le

  /-- **Closedness ⟺ `a = box a`**: combining `Closed a` (`a ≤ box a`) with
  the S4 counit `box_le_self` (`box a ≤ a`) yields equality, and conversely
  equality trivially gives closedness (Paper 2026, p. 76:16: "relations `a`
  such that `a ≤ □a` (and thus `□a = a`)"). -/
  theorem closed_iff_eq_box {X : A} (a : X ⟶ X) :
    Closed a ↔ a = box a := by
      refine ⟨fun h => le_antisymm h (box_le_self a), fun h => ?_⟩
      show a ≤ box a
      exact h.le

end Allegory.TRA
