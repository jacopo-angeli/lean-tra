import Allegory.TRA.Evaluation.BigStep
import Mathlib.Order.FixedPoints

/-!
# S1 — b-Simulation, Similarity `b⪆`, Bisimilarity `b=∼`

Defines applicative b-simulation and the greatest-fixed-point similarity and
bisimilarity relative to a candidate `b` (Gavazzo, LICS 2026, Definition 32 and
§6.1). Concretely, `B(a) := (b⪆ ; a) ← b⪆`; `a` is a b-simulation iff
`a ≤ B(♢a)`; similarity is `b⪆ := νx. B(♢x)`; open similarity is
`♢b⪆ := νx. ♢B(x)`; bisimilarity is `b=∼ := νx. ♢x ⊓ B(♢x°)°`. These are the
objects refined by the op-Howe extension (S2) and proved congruent by Theorem 35
(S4) in this directory.

## Main definitions

* `Allegory.TRA.leftResidual` — allegory division residual `c ← a`
* `Allegory.TRA.simulationFunctional` — `B(a) := (b ; a) ← b`
* `Allegory.TRA.BSimulation` — predicate `a ≤ B(♢a)`
* `Allegory.TRA.similarityMap` — monotone endofunction `x ↦ B(♢x)`
* `Allegory.TRA.similarity` — `b⪆ := νx. B(♢x)`
* `Allegory.TRA.openSimilarity` — `♢b⪆ := νx. ♢B(x)`
* `Allegory.TRA.bisimilarity` — `b=∼ := νx. ♢x ⊓ B(♢x°)°`

## Main results

* `Allegory.TRA.similarity_closed` — `□b⪆ = b⪆`
* `Allegory.TRA.similarity_transitive` — `b⪆ ; b⪆ ≤ b⪆`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 32 / §6.1
* Abramsky, S., *The lazy lambda calculus*, 1990
* Howe, D., *Proving congruence of bisimulation in functional programming languages*, 1996
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **Left residual** `c ← a` (Allegory division: `b ; a ≤ c ↔ b ≤ c ← a`). -/
def leftResidual {X : A} (_c _a : X ⟶ X) : X ⟶ X :=
  -- deps: unknown
  -- TODO
  sorry

/-- **Simulation functional** `B(a) := (b ; a) ← b` parameterised by the
candidate similarity relation `b` (Paper 2026, Sec. 6.1). -/
def simulationFunctional {X : A} (b a : X ⟶ X) : X ⟶ X :=
  leftResidual (b ≫ a) b

/-- **b-simulation** (Paper 2026, Def. 32): `a` is a b-simulation
relative to candidate `b` iff `a ≤ B(♢a)`. -/
def BSimulation {X : A} (b a : X ⟶ X) : Prop :=
  a ≤ simulationFunctional b (openExt a)

/-- The monotone endofunction `x ↦ B(♢x)` whose greatest fixed point
defines similarity (Paper 2026, Def. 32). -/
def similarityMap {X : A} (b : X ⟶ X) : (X ⟶ X) →o (X ⟶ X) where
  toFun x := simulationFunctional b (openExt x)
  monotone' := by
    -- deps: unknown
    -- TODO
    sorry

/-- **Similarity** `b⪆ := νx. B(♢x)` (Paper 2026, Def. 32). -/
def similarity {X : A} (b : X ⟶ X) : X ⟶ X :=
  OrderHom.gfp (similarityMap b)

/-- **Open similarity** `♢b⪆ := νx. ♢B(x)` (Paper 2026, Def. 32). -/
def openSimilarity {X : A} (b : X ⟶ X) : X ⟶ X :=
  openExt (similarity b)

/-- **Bisimilarity** `b=∼ := νx. ♢x ⊓ B(♢x°)°` (Paper 2026, Def. 32). -/
def bisimilarity {X : A} (_b : X ⟶ X) : X ⟶ X :=
  -- deps: unknown
  -- TODO
  sorry

/-- **Similarity is closed**: `□b⪆ = b⪆` (Paper 2026, Sec. 6.1,
"b⪆ is complete (i.e. □b⪆ = b⪆)"). -/
theorem similarity_closed {X : A} (b : X ⟶ X) : Closed (similarity b) := by
  -- deps: OrderHom.gfp, OrderHom.map_gfp, closed_iff_eq_box, box_gfp_eq_gfp_box
  sorry

/-- **Similarity is transitive**: `b⪆ ; b⪆ ≤ b⪆` (Paper 2026, Sec. 6.1,
"b⪆;b⪆ ≤ b⪆"). -/
theorem similarity_transitive {X : A} (b : X ⟶ X) :
    similarity b ≫ similarity b ≤ similarity b := by
  -- deps: OrderHom.le_gfp, OrderHom.gfp, similarityMap, simulationFunctional
  sorry

end Allegory.TRA
