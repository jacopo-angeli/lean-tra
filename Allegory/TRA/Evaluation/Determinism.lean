import Allegory.TRA.Evaluation.Proposition29

/-!
# B4 — Theorem 31: Determinism of Big-Step Evaluation

Closed deterministic ground reductions induce deterministic big-step evaluation
(Gavazzo, LICS 2026, Theorem 31): `a;a° ≤ Δ ⟹ a⇓°;a⇓ ≤ Δκ`. This is the new
result that feeds clause (ii) of the Bridge Theorem (M2) in
`Allegory/TRA/Bridge.lean`. The proof goes through an inversion lemma and a
converse-absorption step, both isolated as separate theorems for re-use.

## Main results

* `Allegory.TRA.bigStep_inversion` — inversion lemma `⟨b⟩ ; a⇓ ≤ ⟨b ; a⇓⟩ ; a⇓` under GIP
* `Allegory.TRA.bigStep_converse_absorb` — converse-absorption `a° ; a⇓ ≤ a⇓` from GIP + determinism
* `Allegory.TRA.bigStep_deterministic` — Theorem 31: closed + reduction + GIP + determinism ⟹ `a⇓° ; a⇓ ≤ Δκ`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Theorem 31
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **Inversion lemma for big-step evaluation** (Paper 2026, Thm. 31
proof, step 1): if `a` satisfies GIP then
`⟨b⟩ ; a⇓ ≤ ⟨b ; a⇓⟩ ; a⇓` for every `b`. -/
theorem bigStep_inversion {X : A} (a b : X ⟶ X) (_hGIP : GIP a) :
    bracketSingle b ≫ bigStep a
      ≤ bracketSingle (b ≫ bigStep a) ≫ bigStep a := by
  -- deps: bigStep_eq_lfp, OrderHom.map_lfp, gip_eq, bracketRel_substitution_distrib
  sorry

/-- **Converse-absorption** (Paper 2026, Thm. 31 proof, step 2):
from the inversion lemma and `a;a° ≤ Δ`, derive `a° ; a⇓ ≤ a⇓`. -/
theorem bigStep_converse_absorb {X : A} (a : X ⟶ X)
    (_hGIP : GIP a) (_hDet : a ≫ converse a ≤ 𝟙 X) :
    converse a ≫ bigStep a ≤ bigStep a := by
  -- deps: bigStep_inversion, bigStep_eq_lfp, Allegory.modular_law, Allegory.converse_involution
  sorry

/-- **Theorem 31** (Paper 2026, p. 76:22) — main determinism result:
closed deterministic ground reductions induce deterministic big-step
evaluation. -/
theorem bigStep_deterministic {X : A} (a : X ⟶ X)
    (_hClosed : Closed a) (_hRed : Reduction a) (_hGIP : GIP a)
    (_hDet : a ≫ converse a ≤ 𝟙 X) :
    converse (bigStep a) ≫ bigStep a ≤ delta_kappa := by
  -- deps: bigStep_converse_absorb, bigStep, closed_bigStep, delta_kappa, delta_kappa_coreflexive, Allegory.converse_composition, Allegory.converse_involution, OrderHom.lfp_le
  sorry

end Allegory.TRA
