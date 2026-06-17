import Allegory.TRA.Basic

/-!
# R1 — Reduction

A relation `a` is a reduction when `Δη ; a = ⊥` (Gavazzo, LICS 2026,
Definition 17), expressing that variables are not reducible. This is the
standard nontriviality condition imported from Bezem et al. 2003 and made part
of the TRA-level vocabulary used by every confluence and orthogonality argument
in the reduction layer.

## Main definitions

* `Allegory.TRA.Reduction` — predicate `Δη ; a = ⊥` characterising reductions

## Main results

* `Allegory.TRA.reduction_le` — inequality form `Δη ; a ≤ ⊥`
* `Allegory.TRA.reduction_bot` — the bottom relation is a reduction

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 17
* Bezem et al., *Term Rewriting Systems*, Cambridge, 2003
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A]

/-- **R1 — Reduction** (Paper 2026, Def. 17): `a : X ⟶ X` is a reduction
when `Δη ; a = ⊥`, i.e. every `a`-related pair has a non-variable in its
domain. Ensures substitution instances of the rule only apply at non-
variable positions. -/
def Reduction {X : A} (a : X ⟶ X) : Prop :=
  delta_eta ≫ a = ⊥

/-- **Reductions absorb variables on the left**: `Δη ; a ≤ ⊥` (the `≤`
form of `Reduction`), useful in chains where the equality is not needed. -/
theorem reduction_le {X : A} (a : X ⟶ X) (h : Reduction a) :
    delta_eta ≫ a ≤ ⊥ :=
  h.le

/-- **Bottom is a reduction** (trivial example, used to lift facts about
arbitrary morphisms to facts about reductions): `Δη ; ⊥ = ⊥`. -/
theorem reduction_bot {X : A} : Reduction (⊥ : X ⟶ X) := by
  -- deps: LocallyCompleteAllegory.comp_iSup_right, iSup_of_empty, Set.iSup_const_bot
  sorry

end Allegory.TRA
