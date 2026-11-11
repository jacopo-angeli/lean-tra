/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Instances.Lambda.OperationalDecomposition
public import LeanTra.TRA.Modality
public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Metatheory.Confluence.ParallelReduction
public import LeanTra.Metatheory.Confluence.Local
public import LeanTra.Metatheory.Confluence.Orthogonal
public import LeanTra.Metatheory.Determinism.BigStep

/-!
# β-reduction

β-reduction on `TrmRel`, the rule-level local hypotheses it satisfies, and the concrete
confluence and big-step determinism results derived from the abstract metatheory.

## Main definitions
* `TrmRel.betaRule`: β-reduction as an arity-indexed `TrmRel`.

## Main statements
* `TrmRel.betaRule_isReduction`, `TrmRel.betaRule_isSubstitutiveAtIdentity`,
  `TrmRel.betaRule_isDeterministic`, `TrmRel.betaRule_gip`, `TrmRel.betaRule_gcp`:
  the five rule-level local hypotheses required by the bridge theorem.
* `TrmRel.betaRule_local_confluent`: confluence of parallel β-reduction via
  `LeanTra.Confluence.local_confluence`.
* `TrmRel.betaRule_confluent_orthogonal`: the orthogonality route to confluence.
* `TrmRel.betaRule_bigStep_determinism`: determinism of big-step β-evaluation on the
  closed part of β.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale TRA
open LeanTra.Algebra

namespace LeanTra.Instances.Lambda
namespace TrmRel

/-! ### β-reduction

β-reduction is introduced as `betaRule`: an arity-indexed relation
that fires whenever its left-hand side is a genuine β-redex, i.e. an
application of a λ-abstraction. Its first property, the one that
qualifies it as a *reduction* in the sense of
`Metatheory/Confluence/ParallelReduction.lean`, is that its left-hand
side is never a variable, so parallel reduction commutes with
substitution. That single fact is proved here; the four remaining
rule-level hypotheses live in the next sub-section. -/

/-- β-reduction: at every arity, the pair `(app (lam t) s, subst0 t s)`. -/
def betaRule : TrmRel := {
  rel := fun n u v => ∃ t s, u = Lam.app (Lam.lam t) s ∧ v = Lam.subst0 t s
  ren_closed := by
    intro n m f u v h
    obtain ⟨t, s, hu, hv⟩ := h
    refine ⟨t.ren (Lam.liftRen f), s.ren f, ?_, ?_⟩
    · rw [hu]; rfl
    · rw [hv]
      unfold Lam.subst0
      rw [Lam.ren_subst, Lam.subst_ren]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; rfl }

/-- `simp`-normal shape of `betaRule`. -/
@[simp] theorem betaRule_rel {n} {u v : Lam n} :
    (betaRule : TrmRel).rel n u v ↔
      ∃ t s, u = Lam.app (Lam.lam t) s ∧ v = Lam.subst0 t s := Iff.rfl

/-- β is a reduction: its left-hand side is never a variable. -/
theorem betaRule_isReduction :
    LeanTra.Confluence.IsReduction (betaRule : TrmRel) := by
  change (varDiag * betaRule : TrmRel) = ⊥
  ext n u v
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨w, ⟨x, _, rfl⟩, t, s, hw, _⟩
  cases hw

/-! ### Local hypotheses for β

Four rule-level properties remain to be checked (the fifth,
`betaRule_isReduction`, is proved just above), and the point of the
whole local formulation is that all four are visibly local: each
speaks only about `betaRule` itself, and none of them mentions parallel
reduction. First, `betaRule` is *substitutive at identity*
(`IsSubstitutiveAtIdentity`), which says that its base substitution
instance is bounded by itself: pre-composing β with a substitution
does not conjure β-redexes that were not already present. Second, β is
*deterministic on the nose* (`IsDeterministic`): two β-reducts of the
same term agree, because both are determined by the outermost
`app (lam ·) ·` whose sub-parts are unique. Third, β satisfies the
*Gentzen Inversion Principle* (`GIP`), which says that β can fire only
after its inspected argument holds a constructor, a `lam` in the
major slot of the application. Fourth, β satisfies the *Gentzen
Conservation Principle* (`GCP`), which says that firing β commutes
with substitution up to the appropriate relational bound. All four are
proved here by direct term-level computation. -/

/-- β is substitutive at the identity: `β⟦Δ⟧ ≤ β`.  If a β-redex can
be exhibited as a substitution-instance of another β-redex with
`τ = σ`, then the outer redex is itself a β-redex, and its reduct is
the outer's `subst0`. -/
theorem betaRule_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (betaRule : TrmRel) := by
  change (TRA.subst betaRule 1 : TrmRel) ≤ betaRule
  rintro m u v ⟨n, t, s, τ, σ, rfl, rfl, ⟨t', s', rfl, rfl⟩, hψ⟩
  -- `τ = σ` pointwise since `1.rel n = (· = ·)`.
  have hτσ : τ = σ := funext (fun x => hψ x)
  subst hτσ
  -- After substituting `τ`, `(app (lam t') s').subst τ` is a β-redex
  -- whose reduct is `subst0 (t'.subst (liftSubst τ)) (s'.subst τ)`, and
  -- that must equal `(subst0 t' s').subst τ`.
  refine ⟨t'.subst (Lam.liftSubst τ), s'.subst τ, ?_, ?_⟩
  · rfl
  · -- Goal: `(Lam.subst0 t' s').subst τ = Lam.subst0 (t'.subst (liftSubst τ)) (s'.subst τ)`.
    show (Lam.subst0 t' s').subst τ
         = Lam.subst0 (t'.subst (Lam.liftSubst τ)) (s'.subst τ)
    unfold Lam.subst0
    rw [Lam.subst_comp, Lam.subst_comp]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      change τ j = ((τ j).ren Fin.succ).subst (Fin.cases (s'.subst τ) Lam.var)
      rw [Lam.subst_ren]
      exact (Lam.subst_id (τ j)).symm

/-- β is deterministic: `βᵒ * β ≤ Δ`. Two β-reducts of the same term
agree, because both are determined by the outermost `app (lam ·) ·`
whose sub-parts are unique. -/
theorem betaRule_isDeterministic :
    LeanTra.Algebra.IsDeterministic (betaRule : TrmRel) := by
  change ((betaRule : TrmRel)ᵒ * betaRule) ≤ 1
  rintro n u v ⟨w, ⟨t, s, hw, rfl⟩, ⟨t', s', hw', rfl⟩⟩
  -- w = app (lam t) s = app (lam t') s'; conclude t = t' and s = s'.
  have h_app : Lam.app (Lam.lam t) s = Lam.app (Lam.lam t') s' := hw.symm.trans hw'
  obtain ⟨h_ls, rfl⟩ := (Lam.app.injEq _ _ _ _).mp h_app
  have h_ls_body : t = t' := Lam.lam.inj h_ls
  subst h_ls_body
  rfl

/-- Gentzen Inversion for β: every β-step factors on the left through
`ε(ι Δ, Δ)`, an elimination whose major slot holds an introduction
form. The redex is `app (lam t) s`, an `app` with `lam t` in the
major slot, `s` in the minor. -/
theorem betaRule_gip : LeanTra.Metatheory.GIP (betaRule : TrmRel) := by
  change (betaRule : TrmRel)
       ≤ OperationalDecomposition.elimination
           (OperationalDecomposition.introduction 1) 1 * betaRule
  rintro n u v ⟨t, s, rfl, rfl⟩
  refine ⟨Lam.app (Lam.lam t) s, ?_, ?_⟩
  · -- (ε(ι Δ, Δ)) at (app (lam t) s, app (lam t) s):
    refine ⟨Lam.lam t, s, Lam.lam t, s, rfl, rfl, ?_, rfl⟩
    -- ι Δ at (lam t, lam t): major slot is `lam` on both sides with equal body.
    exact ⟨t, t, rfl, rfl, rfl⟩
  · exact ⟨t, s, rfl, rfl⟩

/-- Gentzen Conservation for β: for every compatible `x`, β commutes
with `x`-refinement of arguments in the sense that `ε(⌃x, x) * β ≤
β * x⟦x⟧`. Two β-redexes whose `lam`-bodies are `x`-related and whose
arguments are `x`-related have `x⟦x⟧`-related reducts. -/
theorem betaRule_gcp : LeanTra.Metatheory.GCP (betaRule : TrmRel) := by
  intro x hxComp
  change OperationalDecomposition.elimination (TRA.cr x) x * (betaRule : TrmRel)
       ≤ betaRule * TRA.subst x x
  -- IsCompatible x = ⌃x ≤ x = (varDiag ⊔ scr x ≤ x), so varDiag ≤ x
  -- (needed for reflexivity of `x` on variables in the reduct pairing).
  have hvar_le : (varDiag : TrmRel) ≤ x := le_sup_left.trans hxComp
  rintro n u v ⟨w, ⟨t₁, t₂, s₁, s₂, rfl, hw, hcr, hx⟩, tβ, sβ, hβw, rfl⟩
  -- hw : w = app s₁ s₂; hβw : w = app (lam tβ) sβ.
  -- ⇒ s₁ = lam tβ and s₂ = sβ.
  have h_app : Lam.app s₁ s₂ = Lam.app (Lam.lam tβ) sβ := hw.symm.trans hβw
  have hs12 : s₁ = Lam.lam tβ ∧ s₂ = sβ := (Lam.app.injEq _ _ _ _).mp h_app
  obtain ⟨rfl, rfl⟩ := hs12
  -- Now hcr : (TRA.cr x).rel n t₁ (lam tβ).
  -- Cases on hcr, either varDiag (impossible against a lam) or scr,
  -- and scr's lam clause is the only surviving shape.
  rcases hcr with ⟨y, _, hly⟩ | ⟨t₁', ly, ht₁_eq, hly, hbody⟩
                | ⟨_, _, _, _, _, hlam_eq_app, _, _⟩
  · cases hly
  · -- t₁ = lam t₁'; lam-equation: lam tβ = lam ly ⇒ tβ = ly.
    subst ht₁_eq
    have h_body : tβ = ly := Lam.lam.inj hly
    -- Goal uses `tβ.subst0 s₂`; rewrite that endpoint to use `ly`.
    refine ⟨Lam.subst0 t₁' t₂, ⟨t₁', t₂, rfl, rfl⟩, ?_⟩
    change (subst x x).rel n (Lam.subst0 t₁' t₂) (Lam.subst0 tβ s₂)
    rw [h_body]
    unfold Lam.subst0
    refine ⟨n + 1, t₁', ly, Fin.cases t₂ Lam.var, Fin.cases s₂ Lam.var,
            rfl, rfl, hbody, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hx
    · intro j
      exact hvar_le _ _ _ ⟨j, rfl, rfl⟩
  · cases hlam_eq_app

/-! ### Confluence of parallel β-reduction, via `local_confluence`

The payoff. Once the five rule-level facts above are in hand, the
bridge theorem `LeanTra.Confluence.local_confluence` of
`Metatheory/Confluence/Local.lean` applies verbatim and yields
confluence of parallel β-reduction: whenever a term rewrites in two
different ways under `parRed betaRule`, the two results can be joined
by another pair of parallel reductions. No further hand-computation on
terms is needed; the argument is entirely inside the abstract theory,
and the only work that happened in this file is the discharge of its
hypotheses. -/

/-- Unconditional confluence of parallel β-reduction. -/
theorem betaRule_local_confluent :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (betaRule : TrmRel)) :=
  LeanTra.Confluence.local_confluence
    betaRule_isReduction
    betaRule_isSubstitutiveAtIdentity
    betaRule_isDeterministic
    betaRule_gip
    betaRule_gcp

/-! ### Alternative route: via orthogonality

As a secondary demonstration we record the same conclusion reached
along the alternative route that assumes *orthogonality* of the rule
directly. Orthogonality is not a local condition: its second conjunct
mentions `parRed betaRule` itself, so verifying it would require
reasoning about the very object the theorem is about, and it is
therefore taken as an unproved hypothesis here. The two routes share
nothing except the TRA instance, and their coexistence in one file is
a small piece of evidence that the abstract framework really does
modularise the confluence argument. -/

/-- Confluence via orthogonality, needs `IsOrthogonal` as a hypothesis. -/
theorem betaRule_confluent_orthogonal
    (horth : LeanTra.Confluence.IsOrthogonal (betaRule : TrmRel)) :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (betaRule : TrmRel)) :=
  LeanTra.Confluence.orthogonality_confluence betaRule_isReduction horth

/-! ### Determinism of big-step β-evaluation

The metatheorem `LeanTra.Determinism.bigStep_determinism` concludes
`(a^⇓)ᵒ * a^⇓ ≤ Δκ` from `GIP`, `IsClosed` and `IsDeterministic` of
the rule. Plain `betaRule` does not satisfy `IsClosed`: it fires
between open terms too. The natural instantiation is on the closed
part of β, `□ betaRule`, which relates only closed terms; its three
hypotheses are discharged here. `IsClosed (□ betaRule)` is
`TRA.box_isClosed`. `IsDeterministic (□ betaRule)` follows from
`betaRule_isDeterministic` and `TRA.box_le`. `GIP (□ betaRule)` is
proved directly by the same term-level argument as `betaRule_gip`,
adapted to carry the closedness bookkeeping through the two `j`
factors of `TRA.box`. The final theorem
`betaRule_bigStep_determinism` is then a one-line application of
the metatheorem. -/

/-- Gentzen inversion for closed β: every closed β-step factors on
the left through an elimination with an introduction form in the
major slot, with the closedness of the source preserved. Same
argument as `betaRule_gip`, threading closedness through the two `j`
factors of `TRA.box`. -/
theorem betaRule_boxed_gip :
    LeanTra.Metatheory.GIP (TRA.box (betaRule : TrmRel)) := by
  change (TRA.box (betaRule : TrmRel))
       ≤ OperationalDecomposition.elimination
           (OperationalDecomposition.introduction 1) 1 * TRA.box betaRule
  rintro n u v ⟨w, ⟨w', ⟨rfl, u₀, hu_close⟩, t, s, hu_eq, rfl⟩,
                    ⟨rfl, v₀, hw_close⟩⟩
  subst hu_eq
  refine ⟨Lam.app (Lam.lam t) s, ?_, ?_⟩
  · -- Redex-shape witness at (u, u) ∈ ε(ι Δ, Δ).
    refine ⟨Lam.lam t, s, Lam.lam t, s, rfl, rfl, ?_, rfl⟩
    exact ⟨t, t, rfl, rfl, rfl⟩
  · -- Repackage the original hypothesis as `j * β * j`.
    refine ⟨Lam.subst0 t s,
            ⟨Lam.app (Lam.lam t) s, ⟨rfl, u₀, hu_close⟩,
              t, s, rfl, rfl⟩,
            ⟨rfl, v₀, hw_close⟩⟩

/-- Closed β is deterministic: `(□β)ᵒ * □β ≤ 1`. Immediate from
`betaRule_isDeterministic` and the deflationarity `□a ≤ a` on both
sides. -/
theorem betaRule_boxed_isDeterministic :
    LeanTra.Algebra.IsDeterministic (TRA.box (betaRule : TrmRel)) := by
  change ((TRA.box (betaRule : TrmRel))ᵒ * TRA.box betaRule) ≤ 1
  calc (TRA.box (betaRule : TrmRel))ᵒ * TRA.box betaRule
      ≤ (betaRule : TrmRel)ᵒ * TRA.box betaRule :=
        mul_le_mul' (IsInvolutiveQuantale.converse_monotonicity (TRA.box_le _)) le_rfl
    _ ≤ (betaRule : TrmRel)ᵒ * betaRule :=
        mul_le_mul' le_rfl (TRA.box_le _)
    _ ≤ 1 := betaRule_isDeterministic

/-- **Determinism of big-step β-evaluation.** For the closed part of
β, `(β^⇓)ᵒ * β^⇓ ≤ Δκ`. Direct instantiation of
`LeanTra.Determinism.bigStep_determinism` at `TRA.box betaRule`, with
the three hypotheses discharged just above. -/
theorem betaRule_bigStep_determinism :
    (LeanTra.Determinism.bigStepEvaluation (TRA.box (betaRule : TrmRel)))ᵒ
        * LeanTra.Determinism.bigStepEvaluation (TRA.box betaRule)
      ≤ (OperationalDecomposition.valueCoreflexive : TrmRel) :=
  LeanTra.Determinism.bigStep_determinism
    betaRule_boxed_gip
    (TRA.box_isClosed _)
    betaRule_boxed_isDeterministic

end TrmRel
end LeanTra.Instances.Lambda
