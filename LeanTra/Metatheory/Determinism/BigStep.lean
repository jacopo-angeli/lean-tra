/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Determinism.Evaluation
public import LeanTra.Algebra.Diamond

/-!
# Determinism of big-step evaluation

`Metatheory/Determinism/Evaluation.lean` defines `oneStepEvaluation` and
its Kleene closure `bigStepEvaluation`, and states the fixed-point
equations and induction principles they satisfy. The theorem of this
file records what those definitions are for: a rule that is a closed
reduction, that satisfies Gentzen's inversion principle, and that is
deterministic in the sense `aᵒ * a ≤ Δ` induces a big-step evaluation
that is deterministic too. Read relationally, any two outcomes of
evaluating a common source coincide, and their common value is a
closed introduction form.

The hypotheses match those of Theorem 31 in the reference. `IsClosed a`
is the closed-reduction condition; `GIP a` is the standing assumption
of §5.1.2.2 there; and `IsDeterministic a` is the paper's `aᵒ * a ≤ Δ`,
with the composition order corrected against the typo of the appendix.
None of the other appendix conditions — closed inversion, closed
compatibility, the equational form of Proposition 29 — is needed.

The argument is organised in two layers. The bottom layer collects the
infrastructure `a^⇓` obeys once `GIP` and closedness are in force:
Δ̄-inertness at three granularities, prefix absorption of the rule,
one-step unfolding of a big-step run in two forms, and the compound
induction principle on `a^⇓` and its converse. That layer occupies the
first block of `have`s in the proof below. The top layer is the
argument proper, in three stages marked by the separators: absorption
of the reversed rule under the evaluation, inversion for big-step runs
that upgrades the major slot from `⟨a^E⟩` to `⟨a^⇓⟩`, and uniqueness
at the reached canonical form via the converse induction principle
applied at the residual `a^⇓ ⇨ₗ Δκ`.

The closedness hypothesis is spent in exactly one place — the derivation
of the closed-inversion factorisation `a ≤ ⟨Δκ⟩ * a`, which is the
algebraic reading of the reference's "closed reduction" condition and
what promotes the major slot in the second stage. The derivation uses
`box_absorption_right` and the operational decomposition axiom
`box_elimination_oplaxity` (`□⟨x⟩ ≤ ⟨□x⟩`) and nothing else.

The reference's Proposition 29 states `a^⇓` as the least fixed point
of `x = Δκ ∨ ⟨x⟩ ; a ; x`; only the `(≤)` direction is used below and
only that direction holds. The `(≥)` direction is refutable already in
the λ-calculus: with `I = λx.x` and `s` a value, `app(I(II), s)`
admits no `a^E`-step — its major requires two firings at the outer
spine level before becoming a λ — yet the right-hand side relates it
to a value.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale TRA
open LeanTra.Algebra
open LeanTra.Metatheory
open OperationalDecomposition

namespace LeanTra.Determinism

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

/-! ### Determinism of big-step evaluation

The single theorem the file exists to prove. Its three hypotheses are
those of the reference's Theorem 31: closedness of the rule, Gentzen's
inversion principle, and the determinism inequality. The proof runs in
three stages, marked by the separators inside it. The infrastructure
the three stages consume — Δ̄-inertness of `a^E` at three
granularities, prefix absorption `a * a^⇓ ≤ a^⇓`, one-step unfolding
of `a^⇓` in two forms, and the compound induction principle on `a^⇓`
and its converse — is established as a block of `have`s at the head of
the proof. -/

theorem bigStep_determinism {a : α}
    (hgip : GIP a)
    (hclosed : TRA.IsClosed a)
    (hdet : IsDeterministic a) :
    (bigStepEvaluation a)ᵒ * bigStepEvaluation a ≤ (valueCoreflexive : α) := by
  -- Δ̄-inertness under `a^E`
  --
  -- Under `GIP` a rule fires only through an elimination form, so an
  -- introduction form contributes to `a^E` solely via the reflexive summand of
  -- the fixed-point equation. The five inequalities below package the resulting
  -- inertness at three granularities: one step, its Kleene star, and the whole
  -- of `a^⇓`. Every statement is in terms of `Δ̄` because that is what `a^E`
  -- genuinely contains; the transition to the tighter `Δκ` happens only at the
  -- end of a run, through the final filter of `a^⇓`. Together with the
  -- containments `Δ̄ ≤ a^E` and `a ≤ a^E`, these are the elementary facts every
  -- later step consumes.
  have hD_le_E : (introductionCoreflexive : α) ≤ oneStepEvaluation a :=
    le_sup_left.trans (oneStepEvaluation_fixpoint hgip).ge
  have ha_le_E : a ≤ oneStepEvaluation a :=
    calc a ≤ majorProjection introductionCoreflexive * a := hgip
      _ ≤ majorProjection (oneStepEvaluation a) * a :=
          mul_le_mul'
            (majorProjection_monotonicity hD_le_E) le_rfl
      _ ≤ oneStepEvaluation a :=
          le_sup_right.trans (oneStepEvaluation_fixpoint hgip).ge
  have hD_mul_E : (introductionCoreflexive : α) * oneStepEvaluation a
                ≤ introductionCoreflexive := by
    conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
    rw [Quantale.mul_sup_distrib]
    refine sup_le introductionCoreflexive_mul_self.le ?_
    calc (introductionCoreflexive : α)
            * (majorProjection (oneStepEvaluation a) * a)
        = (introductionCoreflexive : α) * majorProjection (oneStepEvaluation a) * a := by
          rw [mul_assoc]
      _ ≤ (⊥ : α) * a := by
          refine mul_le_mul' ?_ le_rfl
          change OperationalDecomposition.introduction 1
                * OperationalDecomposition.elimination (oneStepEvaluation a) 1 ≤ ⊥
          exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
      _ = ⊥ := Quantale.bot_mul
      _ ≤ introductionCoreflexive := bot_le
  have hD_mul_starE : (introductionCoreflexive : α) * (oneStepEvaluation a)∗
                    ≤ introductionCoreflexive := by
    refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
    refine LeanTra.Algebra.star_induction
      (a := oneStepEvaluation a)
      (x := (introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) ?_
    refine sup_le ?_ ?_
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      rw [mul_one]
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      calc (introductionCoreflexive : α)
              * (oneStepEvaluation a * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive))
          = ((introductionCoreflexive : α) * oneStepEvaluation a)
              * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) := by
            rw [mul_assoc]
        _ ≤ (introductionCoreflexive : α)
              * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) :=
            mul_le_mul' hD_mul_E le_rfl
        _ ≤ (introductionCoreflexive : α) :=
            Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl
  have hD_mul_bigStep : (introductionCoreflexive : α) * bigStepEvaluation a
                      ≤ (valueCoreflexive : α) := by
    change (introductionCoreflexive : α) * ((oneStepEvaluation a)∗ * valueCoreflexive)
      ≤ (valueCoreflexive : α)
    calc (introductionCoreflexive : α) * ((oneStepEvaluation a)∗ * valueCoreflexive)
        = ((introductionCoreflexive : α) * (oneStepEvaluation a)∗) * valueCoreflexive := by
          rw [mul_assoc]
      _ ≤ (introductionCoreflexive : α) * (valueCoreflexive : α) :=
          mul_le_mul' hD_mul_starE le_rfl
      _ ≤ (1 : α) * (valueCoreflexive : α) :=
          mul_le_mul' OperationalDecomposition.introduction_unit_oplaxity le_rfl
      _ = valueCoreflexive := one_mul _
  -- Prefix absorption
  --
  -- Prefixing a single firing to a big-step run gives a big-step run. Follows
  -- from `a ≤ a^E` and Kleene-star absorption on the left. The dual — reversed
  -- rule absorbed on the left of the run — is the substantive first stage of
  -- the main argument and appears later.
  have ha_mul_bigStep : a * bigStepEvaluation a ≤ bigStepEvaluation a := by
    change a * ((oneStepEvaluation a)∗ * valueCoreflexive)
      ≤ (oneStepEvaluation a)∗ * valueCoreflexive
    calc a * ((oneStepEvaluation a)∗ * valueCoreflexive)
        = a * (oneStepEvaluation a)∗ * valueCoreflexive := by rw [mul_assoc]
      _ ≤ oneStepEvaluation a * (oneStepEvaluation a)∗ * valueCoreflexive :=
          mul_le_mul' (mul_le_mul' ha_le_E le_rfl) le_rfl
      _ ≤ (oneStepEvaluation a)∗ * valueCoreflexive :=
          mul_le_mul' (LeanTra.Algebra.star_absorption_left _) le_rfl
  -- One-step unfolding of `a^⇓`
  --
  -- Two versions of `a^⇓ ≤ Δκ ∨ ⟨-⟩ * a * a^⇓`. The first, `hunfold_E`,
  -- places `a^E` in the major slot and follows from the fixed-point equations
  -- of the Kleene star and of `a^E`; it uses `GIP` alone. The upgrade to
  -- `⟨a^⇓⟩` in the major slot goes through the closed-inversion factorisation
  -- `a ≤ ⟨Δκ⟩ * a`, which is derived from `IsClosed a` and `GIP` via
  -- `box_absorption_right` and `box_elimination_oplaxity` — this is the only
  -- point in the proof where the closedness hypothesis is spent, and it is
  -- the algebraic reading of the reference's "closed reduction" condition.
  -- Only `(≤)` is available; the reverse fails as recorded in the module
  -- docstring.
  have hunfold_E : bigStepEvaluation a
      ≤ (valueCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
    have hstep1 : bigStepEvaluation a
        = (valueCoreflexive : α) ⊔ oneStepEvaluation a * bigStepEvaluation a := by
      change (oneStepEvaluation a)∗ * valueCoreflexive
        = valueCoreflexive ⊔ oneStepEvaluation a * ((oneStepEvaluation a)∗ * valueCoreflexive)
      conv_lhs => rw [LeanTra.Algebra.star_fixpoint]
      rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]
    have hstep2 : oneStepEvaluation a * bigStepEvaluation a
        ≤ (valueCoreflexive : α)
            ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
      conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
      rw [Quantale.sup_mul_distrib]
      refine sup_le ?_ le_sup_right
      exact hD_mul_bigStep.trans le_sup_left
    calc bigStepEvaluation a
        = (valueCoreflexive : α) ⊔ oneStepEvaluation a * bigStepEvaluation a := hstep1
      _ ≤ (valueCoreflexive : α)
            ⊔ ((valueCoreflexive : α)
                ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) :=
          sup_le_sup_left hstep2 _
      _ = (valueCoreflexive : α)
            ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
          rw [← sup_assoc, sup_idem]
  have ha_eq : TRA.box a = a := TRA.isClosed_iff.mp hclosed
  have hcip : a ≤ majorProjection (valueCoreflexive : α) * a := by
    calc a
        = TRA.box a := ha_eq.symm
      _ ≤ TRA.box (majorProjection (introductionCoreflexive : α) * a) :=
          TRA.box_monotonicity hgip
      _ = TRA.box (majorProjection (introductionCoreflexive : α) * TRA.box a) := by
          rw [ha_eq]
      _ = TRA.box (majorProjection (introductionCoreflexive : α)) * TRA.box a := by
          rw [← TRA.box_absorption_right]
      _ = TRA.box (majorProjection (introductionCoreflexive : α)) * a := by
          rw [ha_eq]
      _ ≤ majorProjection (TRA.box (introductionCoreflexive : α)) * a := by
          refine mul_le_mul' ?_ le_rfl
          exact OperationalDecomposition.box_elimination_oplaxity _ _
  have hunfold : bigStepEvaluation a
      ≤ (valueCoreflexive : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a := by
    -- Slot upgrade `⟨a^E⟩ * a ≤ ⟨a^⇓⟩ * a`: insert `⟨Δκ⟩` in front of the
    -- firing via `hcip`, fuse the two major projections, and absorb
    -- `a^E * Δκ` into `(a^E)∗ * Δκ = a^⇓` by extensivity of the star.
    have hslot : majorProjection (oneStepEvaluation a) * a
        ≤ majorProjection (bigStepEvaluation a) * a := by
      calc majorProjection (oneStepEvaluation a) * a
          ≤ majorProjection (oneStepEvaluation a)
              * (majorProjection (valueCoreflexive : α) * a) :=
            mul_le_mul' le_rfl hcip
        _ = (majorProjection (oneStepEvaluation a)
              * majorProjection (valueCoreflexive : α)) * a := by
            rw [← mul_assoc]
        _ = majorProjection (oneStepEvaluation a * valueCoreflexive) * a := by
            rw [majorProjection_compositionality]
        _ ≤ majorProjection (bigStepEvaluation a) * a := by
            refine mul_le_mul' (majorProjection_monotonicity ?_) le_rfl
            change oneStepEvaluation a * valueCoreflexive
              ≤ (oneStepEvaluation a)∗ * valueCoreflexive
            exact mul_le_mul' (LeanTra.Algebra.star_extensivity _) le_rfl
    calc bigStepEvaluation a
        ≤ (valueCoreflexive : α)
            ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := hunfold_E
      _ ≤ (valueCoreflexive : α)
            ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a :=
          sup_le_sup_left (mul_le_mul' hslot le_rfl) _
  -- Induction principles on `a^⇓` and its converse
  --
  -- The big-step evaluation is a Kleene closure composed with a coreflexive
  -- filter, so induction on it combines fixed-point induction on `a^E` with
  -- Kleene-star induction; both are run through the left residual `b ⇨ₗ b`,
  -- the largest relation whose composition with `b` stays inside `b`. The base
  -- condition sits at `Δ̄`, not at `Δκ`: the fixed-point equation of `a^E`
  -- genuinely contains `Δ̄`, so any upper bound of `(a^E)∗` must contain the
  -- whole of `Δ̄`. The final `Δκ` filter of `a^⇓` is folded in at the last step
  -- of the induction, using the deflationarity `Δκ ≤ Δ̄`. The converse mirror
  -- follows by involution alone. Both principles are stated with `b` a
  -- parameter, since Stage 3 will instantiate them at the residual
  -- `a^⇓ ⇨ₗ Δκ`.
  have hind : ∀ {b : α}, (introductionCoreflexive : α) ≤ b → a * b ≤ b →
      majorProjection b * b ≤ b → bigStepEvaluation a ≤ b := by
    intro b hD ha hproj
    have haE : oneStepEvaluation a ≤ b ⇨ₗ b := by
      refine oneStepEvaluation_induction hgip (sup_le ?_ ?_)
      · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
        calc (introductionCoreflexive : α) * b
            ≤ 1 * b :=
              mul_le_mul' OperationalDecomposition.introduction_unit_oplaxity le_rfl
          _ = b := one_mul b
      · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
        have hwD : (b ⇨ₗ b) * (introductionCoreflexive : α) ≤ b :=
          calc (b ⇨ₗ b) * (introductionCoreflexive : α)
              ≤ (b ⇨ₗ b) * b := mul_le_mul' le_rfl hD
            _ ≤ b := Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
        calc majorProjection (b ⇨ₗ b) * a * b
            ≤ majorProjection (b ⇨ₗ b)
                * (majorProjection (introductionCoreflexive : α) * a) * b :=
              mul_le_mul' (mul_le_mul' le_rfl hgip) le_rfl
          _ = (majorProjection (b ⇨ₗ b)
                * majorProjection (introductionCoreflexive : α)) * a * b := by
              rw [← mul_assoc]
          _ = majorProjection ((b ⇨ₗ b) * (introductionCoreflexive : α)) * a * b := by
              rw [majorProjection_compositionality]
          _ ≤ majorProjection b * a * b :=
              mul_le_mul' (mul_le_mul' (majorProjection_monotonicity hwD) le_rfl) le_rfl
          _ = majorProjection b * (a * b) := mul_assoc _ _ _
          _ ≤ majorProjection b * b := mul_le_mul' le_rfl ha
          _ ≤ b := hproj
    have hstar : (oneStepEvaluation a)∗ ≤ b ⇨ₗ b := by
      refine LeanTra.Algebra.star_induction (sup_le ?_ ?_)
      · exact Quantale.leftMulResiduation_le_iff_mul_le.mpr (by rw [one_mul])
      · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
        calc oneStepEvaluation a * (b ⇨ₗ b) * b
            = oneStepEvaluation a * ((b ⇨ₗ b) * b) := mul_assoc _ _ _
          _ ≤ oneStepEvaluation a * b :=
              mul_le_mul' le_rfl (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl)
          _ ≤ b := Quantale.leftMulResiduation_le_iff_mul_le.mp haE
    change (oneStepEvaluation a)∗ * valueCoreflexive ≤ b
    calc (oneStepEvaluation a)∗ * (valueCoreflexive : α)
        ≤ (b ⇨ₗ b) * (valueCoreflexive : α) := mul_le_mul' hstar le_rfl
      _ ≤ (b ⇨ₗ b) * b := mul_le_mul' le_rfl ((TRA.box_le _).trans hD)
      _ ≤ b := Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hindOp : ∀ {b : α}, (introductionCoreflexive : α) ≤ b → b * aᵒ ≤ b →
      b * majorProjection b ≤ b → (bigStepEvaluation a)ᵒ ≤ b := by
    intro b hD ha hproj
    have h : bigStepEvaluation a ≤ bᵒ := by
      refine hind ?_ ?_ ?_
      · rw [← introductionCoreflexive_converse]
        exact IsInvolutiveQuantale.converse_monotonicity hD
      · have h' := IsInvolutiveQuantale.converse_monotonicity ha
        rwa [IsInvolutiveQuantale.converse_compositionality,
            IsInvolutiveQuantale.converse_involutivity] at h'
      · have h' := IsInvolutiveQuantale.converse_monotonicity hproj
        rwa [IsInvolutiveQuantale.converse_compositionality,
            majorProjection_converse] at h'
    have h' := IsInvolutiveQuantale.converse_monotonicity h
    rwa [IsInvolutiveQuantale.converse_involutivity] at h'
  -- The rule reversed is absorbed by evaluation
  --
  -- `aᵒ * a^⇓ ≤ a^⇓`, the fact that reversing a single step of the rule on top
  -- of a big-step run leaves the run unchanged. The converse of `GIP` writes
  -- `aᵒ` as `aᵒ * ⟨Δ̄⟩`, isolating the elimination form the reversed step must
  -- factor through. Unfolding the run once shows that such an elimination, with
  -- an introduction form as its major, can only fire: its resting summand dies
  -- against intro/elim orthogonality, and the two major projections in the
  -- firing summand fuse and collapse through `⟨Δ̄⟩ ≤ 1`. What remains is
  -- `aᵒ * a * a^⇓`, and determinism collapses `aᵒ * a` to the identity.
  have habs : aᵒ * bigStepEvaluation a ≤ bigStepEvaluation a := by
    have hgip_op : aᵒ ≤ aᵒ * majorProjection (introductionCoreflexive : α) := by
      have h := IsInvolutiveQuantale.converse_monotonicity hgip
      rwa [IsInvolutiveQuantale.converse_compositionality, majorProjection_converse,
          introductionCoreflexive_converse] at h
    have hkey : majorProjection (introductionCoreflexive : α) * bigStepEvaluation a
              ≤ a * bigStepEvaluation a := by
      calc majorProjection (introductionCoreflexive : α) * bigStepEvaluation a
          ≤ majorProjection (introductionCoreflexive : α)
              * ((valueCoreflexive : α)
                  ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) :=
            mul_le_mul' le_rfl hunfold_E
        _ = majorProjection (introductionCoreflexive : α) * valueCoreflexive
              ⊔ majorProjection (introductionCoreflexive : α)
                  * (majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) := by
            rw [Quantale.mul_sup_distrib]
        _ ≤ (⊥ : α) ⊔ a * bigStepEvaluation a := by
            refine sup_le_sup ?_ ?_
            · calc majorProjection (introductionCoreflexive : α)
                      * (valueCoreflexive : α)
                  ≤ majorProjection (introductionCoreflexive : α)
                      * (introductionCoreflexive : α) :=
                    mul_le_mul' le_rfl (TRA.box_le _)
                _ ≤ ⊥ := majorProjection_mul_introductionCoreflexive_le_bot _
            · calc majorProjection (introductionCoreflexive : α)
                      * (majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a)
                  = (majorProjection (introductionCoreflexive : α)
                      * majorProjection (oneStepEvaluation a)) * a * bigStepEvaluation a := by
                    rw [← mul_assoc, ← mul_assoc]
                _ = majorProjection ((introductionCoreflexive : α) * oneStepEvaluation a)
                      * a * bigStepEvaluation a := by
                    rw [majorProjection_compositionality]
                _ ≤ majorProjection (introductionCoreflexive : α)
                      * a * bigStepEvaluation a := by
                    refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
                    exact majorProjection_monotonicity hD_mul_E
                _ ≤ 1 * a * bigStepEvaluation a :=
                    mul_le_mul'
                      (mul_le_mul' majorProjection_introductionCoreflexive_le_one le_rfl)
                      le_rfl
                _ = a * bigStepEvaluation a := by rw [one_mul]
        _ = a * bigStepEvaluation a := by rw [bot_sup_eq]
    calc aᵒ * bigStepEvaluation a
        ≤ aᵒ * majorProjection (introductionCoreflexive : α) * bigStepEvaluation a :=
          mul_le_mul' hgip_op le_rfl
      _ = aᵒ * (majorProjection (introductionCoreflexive : α) * bigStepEvaluation a) := by
          rw [mul_assoc]
      _ ≤ aᵒ * (a * bigStepEvaluation a) := mul_le_mul' le_rfl hkey
      _ = (aᵒ * a) * bigStepEvaluation a := (mul_assoc _ _ _).symm
      _ ≤ 1 * bigStepEvaluation a := mul_le_mul' hdet le_rfl
      _ = bigStepEvaluation a := one_mul _
  -- Inversion for big-step runs
  --
  -- `⟨b⟩ * a^⇓ ≤ ⟨b * a^⇓⟩ * a^⇓` for every `b`. The reading: a run starting
  -- from an elimination form whose major stands in relation `b` factors as
  -- "evaluate the major to a value, then take one firing and continue the run".
  -- Uses the second form of one-step unfolding, `hunfold`, which is the only
  -- place `IsClosed a` is spent: the closedness hypothesis turns the `⟨a^E⟩`
  -- of one-step unfolding into `⟨a^⇓⟩`, so the major projection of `b` and
  -- the major projection of the run can fuse. The resting summand `⟨b⟩ * Δκ`
  -- dies by intro/elim orthogonality, and the leading firing left in front
  -- of the fused slot is reabsorbed into the run via `a * a^⇓ ≤ a^⇓`.
  have hinv : ∀ b : α, majorProjection b * bigStepEvaluation a
      ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a := by
    intro b
    refine le_trans (mul_le_mul' le_rfl hunfold) ?_
    rw [Quantale.mul_sup_distrib]
    refine sup_le ?_ ?_
    · calc majorProjection b * (valueCoreflexive : α)
          ≤ majorProjection b * (introductionCoreflexive : α) :=
            mul_le_mul' le_rfl (TRA.box_le _)
        _ ≤ (⊥ : α) := majorProjection_mul_introductionCoreflexive_le_bot _
        _ ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a := bot_le
    · calc majorProjection b
              * (majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a)
          = (majorProjection b * majorProjection (bigStepEvaluation a))
              * a * bigStepEvaluation a := by
            rw [← mul_assoc, ← mul_assoc]
        _ = majorProjection (b * bigStepEvaluation a) * a * bigStepEvaluation a := by
            rw [majorProjection_compositionality]
        _ = majorProjection (b * bigStepEvaluation a) * (a * bigStepEvaluation a) := by
            rw [mul_assoc]
        _ ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a :=
            mul_le_mul' le_rfl ha_mul_bigStep
  -- Uniqueness of the reached canonical form
  --
  -- The theorem is `(a^⇓)ᵒ * a^⇓ ≤ Δκ`. Work at the left residual
  -- `c := a^⇓ ⇨ₗ Δκ`, so that `z ≤ c` is equivalent to `z * a^⇓ ≤ Δκ`; the
  -- counit `hc` records the containment at `c` itself. Applying `hindOp` at
  -- `c` requires three closure properties. The base `Δ̄ ≤ c` is the
  -- Δ̄-inertness `hD_mul_bigStep` transposed along the residual. The
  -- `c * aᵒ ≤ c` step is the absorption `habs` of the first stage, moved past
  -- `c` and folded back through the residual. The `c * ⟨c⟩ ≤ c` step is the
  -- inversion `hinv` of the second stage: `⟨c⟩ * a^⇓ ≤ ⟨c * a^⇓⟩ * a^⇓ ≤
  -- ⟨Δκ⟩ * a^⇓`, which collapses through `⟨Δκ⟩ ≤ ⟨Δ̄⟩ ≤ 1` back to `a^⇓`, and
  -- `c` absorbs `a^⇓` into `Δκ`. The principle yields `(a^⇓)ᵒ ≤ c`, and
  -- transposing that containment back along the residual is the theorem.
  have hc : (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
      * bigStepEvaluation a ≤ (valueCoreflexive : α) :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hmain : (bigStepEvaluation a)ᵒ
      ≤ bigStepEvaluation a ⇨ₗ (valueCoreflexive : α) := by
    refine hindOp ?_ ?_ ?_
    · exact Quantale.leftMulResiduation_le_iff_mul_le.mpr hD_mul_bigStep
    · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      calc (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α)) * aᵒ
              * bigStepEvaluation a
          = (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * (aᵒ * bigStepEvaluation a) := mul_assoc _ _ _
        _ ≤ (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * bigStepEvaluation a := mul_le_mul' le_rfl habs
        _ ≤ valueCoreflexive := hc
    · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      have hproj : majorProjection
            (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
            * bigStepEvaluation a
          ≤ bigStepEvaluation a :=
        calc majorProjection
              (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * bigStepEvaluation a
            ≤ majorProjection
                ((bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
                  * bigStepEvaluation a)
                * bigStepEvaluation a := hinv _
          _ ≤ majorProjection (valueCoreflexive : α) * bigStepEvaluation a :=
              mul_le_mul' (majorProjection_monotonicity hc) le_rfl
          _ ≤ majorProjection (introductionCoreflexive : α) * bigStepEvaluation a :=
              mul_le_mul' (majorProjection_monotonicity (TRA.box_le _)) le_rfl
          _ ≤ 1 * bigStepEvaluation a :=
              mul_le_mul' majorProjection_introductionCoreflexive_le_one le_rfl
          _ = bigStepEvaluation a := one_mul _
      calc (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * majorProjection
                  (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * bigStepEvaluation a
          = (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * (majorProjection
                  (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
                  * bigStepEvaluation a) := mul_assoc _ _ _
        _ ≤ (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
              * bigStepEvaluation a := mul_le_mul' le_rfl hproj
        _ ≤ valueCoreflexive := hc
  calc (bigStepEvaluation a)ᵒ * bigStepEvaluation a
      ≤ (bigStepEvaluation a ⇨ₗ (valueCoreflexive : α))
          * bigStepEvaluation a := mul_le_mul' hmain le_rfl
    _ ≤ valueCoreflexive := hc

end LeanTra.Determinism

#print axioms LeanTra.Determinism.bigStep_determinism
