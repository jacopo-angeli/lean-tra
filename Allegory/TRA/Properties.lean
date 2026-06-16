import Allegory.TRA.Basic

/-!
# Compatible, CUI, Substitutive, Leibniz's Law

This file introduces key predicate-level notions on relations inside a
Term Relation Algebra (Gavazzo, LICS 2026, Definition 15). These notions
classify when a relation is stable under the additional TRA structure: Howe
closure (`ˆ·`), semirelators (`˜·`), and substitution `·[·]`. All definitions
live over a locally complete allegory, so relations form complete lattices and
support joins, composition, and residual reasoning. These predicates are the
language used downstream by the Bridge Theorem and the congruence proofs of
similarity in `Allegory/TRA/Similarity/*`.

## Main definitions

* `Allegory.TRA.Compatible` — closure under Howe extension and diagonal coreflexive
* `Allegory.TRA.ClosedUnderTermConstructs` — closure under semirelator `˜·`
* `Allegory.TRA.Precongruence` — compatible preorder
* `Allegory.TRA.CUI` — closed under substitution instances (`a[Δ] ≤ a`)
* `Allegory.TRA.Substitutive` — closed under self-substitution (`a[a] ≤ a`)
* `Allegory.TRA.Leibniz` — substitution of identity preserves relation

## Main results

* `Allegory.TRA.compatible_reflexive` — compatibility implies reflexivity (`𝟙 ≤ a`)
* `Allegory.TRA.substitution_delta_CUI` — every `a[Δ]` is closed under instances
* `Allegory.TRA.compatible_leibniz` — compatibility implies Leibniz substitution law

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 15
-/

open CategoryTheory

namespace Allegory.TRA

  variable {A : Type*} [TRA A]

  -- A relation `a` is **compatible** when `â ≤ a`, i.e. `(Δη ⊔ ã) ≤ a`
  def Compatible {X : A} (a : X ⟶ X) : Prop := delta_eta ⊔ tilde a ≤ a

  -- A relation `a` is **closed under term constructs** when `ã ≤ a`,
  def ClosedUnderTermConstructs {X : A} (a : X ⟶ X) : Prop := tilde a ≤ a

  /-- A relation `a : X ⟶ X` is a **precongruence** when it is compatible
  and a preorder, i.e. with reflexive (`a ≤ a`) and transitive (`a ≫ a ≤ a`)
  (Paper 2026, Definition 15(iii)).

  The paper's "congruence" further requires symmetry (an *equivalence*); we
  encode the weaker "precongruence" here (preorder + compatible). -/
  def Precongruence {X : A} (a : X ⟶ X) : Prop := Compatible a ∧ 𝟙 X ≤ a ∧ a ≫ a ≤ a

  -- A relation `a` is **closed under (substitution) instances (CUI)** when `a[Δ] ≤ a` - Definition 15(iv)
  def CUI {X Y : A} (a : X ⟶ Y) : Prop := substitution a (𝟙 X) ≤ a

  -- A relation `a : X ⟶ X` is **substitutive** when `a[a] ≤ a` - Definition 15(v).
  def Substitutive {X : A} (a : X ⟶ X) : Prop := substitution a a ≤ a

  -- A relation `a : X ⟶ X` satisfies **Leibniz's Substitution Law** when `Δ[a] ≤ a` - Definition 15(vi).
  def Leibniz {X : A} (a : X ⟶ X) : Prop := substitution (𝟙 X) a ≤ a

  -- **Every compatible relation is reflexive**
  theorem compatible_reflexive {X : A} {a : X ⟶ X} (_h : Compatible a) :
    𝟙 X ≤ a := by
    -- deps: howe_delta, howe_fixed_point, howe_uniqueness, tilde_monotonicity, OrderHom.lfp, OrderHom.lfp_le
    sorry

  -- **For any `a`, the relation `a[Δ]` is always CUI**
  theorem substitution_delta_CUI {X Y : A} (a : X ⟶ Y) :
    CUI (substitution a (𝟙 X)) := by
    -- deps: substitution_assoc, substitution_monotonicity_right, substitution_left_unit, howe_delta, howe_fixed_point, tilde_distributivity
    sorry

  -- **Compatibility implies Leibniz's Substitution Law**
  theorem compatible_leibniz {X : A} {a : X ⟶ X} (_h : Compatible a) :
    Leibniz a := by
    -- deps: substitution_right_residual_adjunction, compatible_reflexive, substitution_left_unit, substitution_tilde_distrib, howe_delta, howe_fixed_point
    sorry

end Allegory.TRA
