import Allegory.LocallyComplete
import Mathlib.Order.FixedPoints

/-!
# R3 — Church–Rosser Property, Diamond Property, Confluence

Defines Church–Rosser, the diamond property, and confluence inside a locally
complete allegory (Gavazzo, LICS 2026, Definition 20), together with the
classical equivalence `CR ⟺ Confluent` due to Struth. Concretely,
Church–Rosser is `(a ∨ a°)* = a* ; a*°`, the diamond property is
`a° ; a ≤ a ; a°`, and confluence is the diamond property of the Kleene star
`a*`. The Kleene star itself is introduced locally as the least fixed point of
`x ↦ Δ ∨ b ; x` until the A2 iteration operator is exposed in
`Allegory/LocallyComplete.lean`.

## Main definitions

* `Allegory.kleeneStarMap` — monotone endofunction `x ↦ Δ ∨ b ; x`
* `Allegory.kleeneStar` — Kleene star `b* = μx. Δ ∨ b ; x`
* `Allegory.ChurchRosser` — Church–Rosser property `(a ∨ a°)* = a* ; a*°`
* `Allegory.Diamond` — diamond property `a° ; a ≤ a ; a°`
* `Allegory.Confluent` — confluence: `a*` has the diamond property

## Main results

* `Allegory.confluent_of_diamond` — diamond ⟹ confluent
* `Allegory.churchRosser_iff_confluent` — CR ⟺ Confluent

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 20
* Church, Rosser, *Some Properties of Conversion*, 1936
* Bezem et al., *Term Rewriting Systems*, Cambridge, 2003
* Struth, G., *Calculating Church–Rosser proofs in Kleene algebra*, 2002/2006
-/

open CategoryTheory Allegory

namespace Allegory

variable {A : Type*} [LocallyCompleteAllegory A]

/-- The monotone endofunction `x ↦ Δ ∨ b ; x` whose least fixed point is
the Kleene star `b*`. Local helper — should ultimately live in
`Allegory/LocallyComplete.lean` as the A2 iteration operator. -/
def kleeneStarMap {X : A} (b : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := 𝟙 X ⊔ b ≫ x
  monotone' := by
    -- deps: sup_le_sup_left, LocallyCompleteAllegory.comp_iSup_right
    sorry

/-- **Kleene star** `b*` = `μx. Δ ∨ b ; x` (Paper 2026, A2 iteration). -/
def kleeneStar {X : A} (b : X ⟶ X) : X ⟶ X :=
  OrderHom.lfp (kleeneStarMap b)

/-- **Church-Rosser property** (Paper 2026, Def. 20):
`(a ∨ a°)* = a* ; a*°`. -/
def ChurchRosser {X : A} (a : X ⟶ X) : Prop :=
  kleeneStar (a ⊔ converse a) = kleeneStar a ≫ converse (kleeneStar a)

/-- **Diamond property** (Paper 2026, Def. 20): `a° ; a ≤ a ; a°`. -/
def Diamond {X : A} (a : X ⟶ X) : Prop :=
  converse a ≫ a ≤ a ≫ converse a

/-- **Confluence** (Paper 2026, Def. 20): `a*` has the diamond property. -/
def Confluent {X : A} (a : X ⟶ X) : Prop :=
  Diamond (kleeneStar a)

/-- **Diamond implies confluent of star** (Paper 2026, p. 76:18:
"Easy algebraic calculations show that if `a` has the diamond property,
then it is confluent"). -/
theorem confluent_of_diamond {X : A} (a : X ⟶ X) (_h : Diamond a) :
    Confluent a := by
  -- deps: Allegory.converse_composition, Allegory.converse_involution, OrderHom.lfp_induction, OrderHom.map_lfp
  sorry

/-- **CR ⟺ Confluent** (Paper 2026, p. 76:18 / Struth [139][140]:
"a relation has the Church-Rosser property iff it is confluent"). -/
theorem churchRosser_iff_confluent {X : A} (a : X ⟶ X) :
    ChurchRosser a ↔ Confluent a := by
  -- deps: Allegory.converse_composition, Allegory.converse_involution, OrderHom.lfp_le, OrderHom.map_lfp, le_antisymm
  sorry

end Allegory
