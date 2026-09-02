/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Evaluation
public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Metatheory.Confluence.Local

/-!
# Determinism of big-step evaluation

Given a closed reduction `a` whose base substitution instance is
target-deterministic (`a * aᵒ ≤ Δ`) and satisfies `GIP`, the induced
big-step evaluation is deterministic up to the value coreflexive:
`(a^⇓)ᵒ * a^⇓ ≤ Δ_κ`.

## Roadmap of the proof

The file is organised in four layers:

1. **Algebraic prerequisites.** Small reusable lemmas about `Δ̄ = ι Δ`
   (the introduction coreflexive), `⟨_⟩ = majorProjection _`, and how
   they interact via the orthogonality / compositionality laws of the
   operational decomposition.

2. **Proposition 29** (paper): a fixed-point characterisation of `a^⇓`
   with `a^⇓` itself in the elimination slot,
   `a^⇓ = Δ̄ ∨ ⟨a^⇓⟩ * a * a^⇓` (and its closed refinement
   `a^⇓ = Δ_κ ∨ ⟨a^⇓⟩ * a * a^⇓` when `a` is closed). This is where
   the interplay between `a^E` and `a^⇓` is crystallised.

3. **The three intermediate steps** of the paper's proof sketch:
   * **Step 1 — Inversion lemma.** From `GIP a`, one derives
     `⟨b⟩ * a^⇓ ≤ ⟨b * a^⇓⟩` for every `b`. (Genuinely inductive.)
   * **Step 2 — Determinism absorbed at the reduction level.** From
     `a * aᵒ ≤ Δ` (together with the inversion lemma from Step 1),
     one derives `aᵒ * a^⇓ ≤ a^⇓`.
   * **Step 3 — Value coreflexive as fixed point.** From
     `aᵒ * a^⇓ ≤ a^⇓` and the closed characterisation of `a^⇓`
     (from layer 2), one derives `(a^⇓)ᵒ * a^⇓ ≤ Δ_κ`.

4. **The main theorem** chaining Steps 1–3.

## Status

**Layer 1**: fully proved (all Δ̄- and `⟨_⟩`-algebra, together with
`Δ_κ * a^E ≤ Δ_κ`, `Δ_κ * (a^E)∗ ≤ Δ_κ`, `Δ_κ * a^⇓ ≤ Δ_κ` —
closedness preservation through big-step evaluation).

**Layer 2 (Prop 29 and F1–F4):**
* **F1** (`valueCoreflexive_le_bigStepEvaluation`): proved.
* **F2** (`rule_mul_bigStepEvaluation_le`): proved.
* **Prop 29 (equational)** (`bigStepEvaluation_fixpoint`): `sorry`.
  Not derivable from `(≤)` and `(≥)` alone — the `(≤)` direction
  uses `⟨a^E⟩` in the elim slot and `a^E ≤ a^⇓` fails in general
  (a single evaluation step need not land at a value). Requires
  F4-style LFP reasoning. **This is now the load-bearing sorry**,
  since F3, Prop 29 (≥), Step 1, and Prop 29 (closed) all reduce
  to it.
* **Auxiliary** (`bigStepEvaluation_mul_self_le`): fully proved
  (`a^⇓ * a^⇓ ≤ a^⇓`). Uses only Δ̄'s absorption laws.
* **F3** (`majorProjection_bigStepEvaluation_mul_bigStepEvaluation_le`):
  proved, conditional on `bigStepEvaluation_fixpoint`. Unfold the
  right `a^⇓` via the fixpoint equation, kill the `⟨a^⇓⟩ * Δ̄`
  summand by orthogonality, fold `⟨a^⇓⟩ * ⟨a^⇓⟩ = ⟨a^⇓ * a^⇓⟩ ≤
  ⟨a^⇓⟩` via the auxiliary, and land back in the fixpoint's
  elim-summand.
* **F4** (`bigStepEvaluation_induction`): `sorry`. Signature now
  correctly requires `SRA.IsClosed a`. The LFP characterisation of
  `a^⇓` needed to close this requires Prop. 5.7 of the draft
  (`□(a^E) = (□a)^E`), which in turn needs an `IsClosedFun`
  transfer of `□` across the `oneStepEvaluation` recursor.
* **Prop 29 (≤)** (`bigStepEvaluation_unfold_le`): proved with
  `⟨a^E⟩` in the elimination slot.
* **Prop 29 (≥)** (`bigStepEvaluation_unfold_ge`): proved,
  conditional on F3.
* **Prop 29 (closed)** (`bigStepEvaluation_fixpoint_closed`):
  `sorry`. Sharpens Δ̄ to Δ_κ under closedness; needs
  `bigStepEvaluation_fixpoint` plus closedness of `a^⇓`.

**Layer 3**:
* **Step 1 (`inversion_bigStep`)**: proved, conditional on
  `bigStepEvaluation_fixpoint`. The proof needs neither closed
  inversion nor closedness — Prop 29's fixpoint equation plus F2
  suffice. The `_hinv` hypothesis is retained for compatibility
  with the main theorem but is unused.
* **Step 2 (`opp_bigStep_le_bigStep`)**: **fully proved sorry-free**.
  Uses only `bigStepEvaluation_unfold_le`, the closed inversion
  principle, and forward determinism `aᵒ * a ≤ 1`. Depends only on
  `[propext, Classical.choice, Quot.sound]`.
* **Step 3 (`bigStep_op_bigStep_le_valueCoreflexive`)**: `sorry`. The
  paper's proof (Thm. A.12 second half in the draft's appendix) uses
  law F9 of Fig. 8 (dual of F4) via a chain of residuations
  `a^⇓ᵒ ≤ Δ_κ ⇨ₗ a^⇓`. F9 does not follow from F4 by mere converse
  — it needs its own LFP argument, of comparable weight.

**Layer 4 (chained `determinism`)**: type-checks. Depends
transitively on the remaining Layer-2 sorries via Step 1 (Prop 29
fixpoint) and Step 3 (Prop 29 closed / F9).

## Roadmap to full closure

The load-bearing prerequisite is **Lemma A.6** of the draft:
for closed `a`, `a^⇓` is the least solution of
`x = Δ_κ ∨ a·x ∨ ⟨x⟩·x`. Once this is formalised, F1–F4 follow
(F1/F2 already proved; F3/F4 need the ⟹/⟸ direction of the LFP
characterisation, respectively). Beyond A.6, one also needs the
dual LFP characterisation for `a^⇓ᵒ` to derive F9, which unblocks
Step 3.

Concretely, in order of expected effort:

1. Prove **Lemma A.6** (~150–250 lines): show
   `a^⇓ = μx. Δ_κ ∨ a·x ∨ ⟨x⟩·x` for closed `a`, using
   `SRA.box_lfp` (transfer of `□` across a closed function) applied
   to the appropriate recursor built from the `oneStepEvaluation`
   fixpoint.
2. **F3, F4** fall out immediately (~10 lines each).
3. **Prop 29 (=/closed)** follow by ≤/≥ pairing (~30 lines).
4. **F9** (dual LFP for `a^⇓ᵒ`) is a mirror of Lemma A.6 for `aᵒ`
   (~50–100 lines using the involutive quantale structure).
5. **Step 3** follows by residuation `a^⇓ᵒ ≤ a^⇓ ⇨ₗ Δ_κ` and F9
   (~30 lines).
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA LeanTra.Algebra
open OperationalDecomposition

namespace LeanTra.Metatheory

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]



/-! ## Layer 1 — Algebraic prerequisites

Small reusable facts about the interaction of `ι Δ = Δ̄`,
`majorProjection = ⟨_⟩`, and the orthogonality / compositionality
laws of the operational decomposition. All proved directly. -/

/-- `Δ̄` (`ι Δ`) is idempotent under composition. -/
theorem introductionCoreflexive_mul_self :
    (introductionCoreflexive : α) * introductionCoreflexive = introductionCoreflexive := by
  change OperationalDecomposition.introduction 1
       * OperationalDecomposition.introduction 1
     = OperationalDecomposition.introduction 1
  rw [← OperationalDecomposition.introduction_compositionality, one_mul]

/-- `Δ̄` is symmetric under converse. -/
@[simp] theorem introductionCoreflexive_converse :
    (introductionCoreflexive : α)ᵒ = introductionCoreflexive := by
  change (OperationalDecomposition.introduction 1)ᵒ
       = OperationalDecomposition.introduction 1
  rw [← OperationalDecomposition.introduction_converse_commutation,
      IsInvolutiveQuantale.converse_one]

/-- Mirror of `introduction_elimination_orthogonality`: an elimination
form followed by an introduction form is empty. Derived by converse. -/
theorem elimination_mul_introduction_le_bot (a b c : α) :
    OperationalDecomposition.elimination a b
      * OperationalDecomposition.introduction c ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_monotonicity_iff,
      IsInvolutiveQuantale.converse_bot_strictness,
      IsInvolutiveQuantale.converse_compositionality,
      ← OperationalDecomposition.introduction_converse_commutation,
      ← OperationalDecomposition.elimination_converse_commutation]
  exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _

/-- The elimination coreflexive followed by an elimination form is
empty on the intro side: `⟨X⟩ * Δ̄ = ⊥`. -/
theorem majorProjection_mul_introductionCoreflexive_le_bot (b : α) :
    majorProjection b * (introductionCoreflexive : α) ≤ ⊥ := by
  change OperationalDecomposition.elimination b 1
       * OperationalDecomposition.introduction 1 ≤ ⊥
  exact elimination_mul_introduction_le_bot _ _ _

/-- `Δ̄ * a ≤ ⊥` for any rule `a` satisfying `GIP`. An introduction
form cannot be reduced by a rule that only fires under an elimination. -/
theorem introductionCoreflexive_mul_rule_le_bot {a : α} (hgip : GIP a) (y : α) :
    OperationalDecomposition.introduction y * a ≤ (⊥ : α) := by
  calc OperationalDecomposition.introduction y * a
      ≤ OperationalDecomposition.introduction y
          * (majorProjection (introductionCoreflexive : α) * a) := by
        exact mul_le_mul' le_rfl hgip
    _ = OperationalDecomposition.introduction y
          * majorProjection (introductionCoreflexive : α) * a := by
        rw [mul_assoc]
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.introduction y
              * OperationalDecomposition.elimination
                  (introductionCoreflexive : α) 1 ≤ ⊥
        exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
    _ = ⊥ := Quantale.bot_mul

/-- The elimination coreflexive on the LEFT of the `⟨_⟩` fusion:
`⟨X⟩ * ⟨Y⟩ = ⟨X * Y⟩`. Direct consequence of `elimination_compositionality`
at `b := Δ = 1`. -/
theorem majorProjection_compositionality (X Y : α) :
    majorProjection X * majorProjection Y = majorProjection (X * Y) := by
  change OperationalDecomposition.elimination X 1
       * OperationalDecomposition.elimination Y 1
     = OperationalDecomposition.elimination (X * Y) 1
  rw [← OperationalDecomposition.elimination_compositionality, one_mul]

/-- `⟨_⟩` commutes with converse: `⟨X⟩ᵒ = ⟨Xᵒ⟩`. -/
@[simp] theorem majorProjection_converse (X : α) :
    (majorProjection X)ᵒ = majorProjection Xᵒ := by
  change (OperationalDecomposition.elimination X 1)ᵒ
       = OperationalDecomposition.elimination Xᵒ 1
  rw [← OperationalDecomposition.elimination_converse_commutation,
      IsInvolutiveQuantale.converse_one]

/-- `⟨_⟩` is monotone. -/
theorem majorProjection_monotonicity ⦃a b : α⦄ (h : a ≤ b) :
    majorProjection a ≤ majorProjection b :=
  elimination_monotonicity h le_rfl



/-! ### Introduction forms are fixed points of evaluation

An introduction form one-step-evaluates only to itself; the same holds
under the reflexive-transitive closure and under `bigStepEvaluation`. -/

/-- `Δ̄ * a^E ≤ Δ̄` under `GIP a`. Starting at an introduction form,
one step of evaluation gives back that same introduction form. -/
theorem introductionCoreflexive_mul_oneStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) * oneStepEvaluation a ≤ introductionCoreflexive := by
  -- Unfold `a^E` via its fixed-point equation, then apply the two
  -- orthogonalities to collapse the resulting cases.
  conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
  rw [Quantale.mul_sup_distrib]
  refine sup_le ?_ ?_
  · exact introductionCoreflexive_mul_self.le
  · calc (introductionCoreflexive : α)
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

/-- `Δ̄ * (a^E)∗ ≤ Δ̄` under `GIP a`. Kleene-star induction, phrased
via right residuation: `(a^E)∗ ≤ Δ̄ ⇨ᵣ Δ̄`. The two premises
`1 ≤ Δ̄ ⇨ᵣ Δ̄` (i.e. `Δ̄ ≤ Δ̄`) and `a^E * (Δ̄ ⇨ᵣ Δ̄) ≤ Δ̄ ⇨ᵣ Δ̄`
(reduces to `Δ̄ * a^E ≤ Δ̄`, provable but on the wrong side; here
we use the left form) — actually we use the left residual to keep
things pointing the right way. -/
theorem introductionCoreflexive_mul_star_oneStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) * (oneStepEvaluation a)∗ ≤ introductionCoreflexive := by
  -- Residuate to `(a^E)∗ ≤ ι Δ ⇨ᵣ ι Δ` and apply `star_induction`.
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine LeanTra.Algebra.star_induction
    (a := oneStepEvaluation a)
    (x := (introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) ?_
  refine sup_le ?_ ?_
  · -- 1 ≤ ι Δ ⇨ᵣ ι Δ  ↔  ι Δ * 1 ≤ ι Δ
    refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    rw [mul_one]
  · -- a^E * (ι Δ ⇨ᵣ ι Δ) ≤ ι Δ ⇨ᵣ ι Δ
    refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    calc (introductionCoreflexive : α)
            * (oneStepEvaluation a * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive))
        = ((introductionCoreflexive : α) * oneStepEvaluation a)
            * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) := by
          rw [mul_assoc]
      _ ≤ (introductionCoreflexive : α)
            * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) := by
          exact mul_le_mul' (introductionCoreflexive_mul_oneStepEvaluation_le hgip) le_rfl
      _ ≤ (introductionCoreflexive : α) :=
          Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl

/-- `Δ̄ * a ≤ ⊥` under `GIP a`. An `a`-step cannot start from an
introduction form: `GIP` forces every `a`-step through an
elimination form, and elim/intro are orthogonal. -/
theorem introductionCoreflexive_mul_rule_orthogonality {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) * a ≤ ⊥ := by
  calc (introductionCoreflexive : α) * a
      ≤ (introductionCoreflexive : α) * (majorProjection (introductionCoreflexive : α) * a) :=
        mul_le_mul' le_rfl hgip
    _ = ((introductionCoreflexive : α) * majorProjection (introductionCoreflexive : α)) * a := by
        rw [mul_assoc]
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.introduction 1
              * OperationalDecomposition.elimination (introductionCoreflexive : α) 1 ≤ ⊥
        exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
    _ = ⊥ := Quantale.bot_mul

/-- `aᵒ * Δ̄ ≤ ⊥` under `GIP a`. Mirror of the previous lemma: an
`a`-step cannot END at an introduction form via `aᵒ` (i.e. `a` does
not produce introduction forms as targets of a reverse step). -/
theorem opp_rule_mul_introductionCoreflexive_orthogonality
    {a : α} (hgip : GIP a) :
    aᵒ * (introductionCoreflexive : α) ≤ ⊥ := by
  -- Converse of the above via involution.
  rw [← IsInvolutiveQuantale.converse_monotonicity_iff,
      IsInvolutiveQuantale.converse_bot_strictness,
      IsInvolutiveQuantale.converse_compositionality,
      introductionCoreflexive_converse,
      IsInvolutiveQuantale.converse_involutivity]
  exact introductionCoreflexive_mul_rule_orthogonality hgip

/-- `Δ_κ * a^E ≤ Δ_κ` under `GIP a`: an evaluation step starting at
a closed value stays a closed value. From the fixed point of `a^E`,
both summands (Δ̄ and ⟨a^E⟩ * a) either preserve Δ_κ (the Δ̄ arm,
since Δ̄ ≤ 1 gives Δ_κ * Δ̄ ≤ Δ_κ) or are killed by intro/elim
orthogonality (the ⟨a^E⟩ * a arm, using Δ_κ ≤ intro 1). -/
theorem valueCoreflexive_mul_oneStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (valueCoreflexive : α) * oneStepEvaluation a ≤ valueCoreflexive := by
  have hDκ_le_intro : (valueCoreflexive : α) ≤ OperationalDecomposition.introduction 1 :=
    SRA.box_le _
  conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
  rw [Quantale.mul_sup_distrib]
  refine sup_le ?_ ?_
  · calc (valueCoreflexive : α) * introductionCoreflexive
        ≤ (valueCoreflexive : α) * 1 := by
          refine mul_le_mul' le_rfl ?_
          exact OperationalDecomposition.introduction_unit_oplaxity
      _ = valueCoreflexive := mul_one _
  · calc (valueCoreflexive : α) * (majorProjection (oneStepEvaluation a) * a)
        = ((valueCoreflexive : α) * majorProjection (oneStepEvaluation a)) * a := by
          rw [mul_assoc]
      _ ≤ (OperationalDecomposition.introduction 1
            * OperationalDecomposition.elimination (oneStepEvaluation a) 1) * a :=
          mul_le_mul' (mul_le_mul' hDκ_le_intro le_rfl) le_rfl
      _ ≤ (⊥ : α) * a := by
          refine mul_le_mul' ?_ le_rfl
          exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
      _ = ⊥ := Quantale.bot_mul
      _ ≤ valueCoreflexive := bot_le

/-- `Δ_κ * (a^E)∗ ≤ Δ_κ` — closedness preserved by any number of
one-step evaluations. Kleene-star induction on the previous lemma. -/
theorem valueCoreflexive_mul_star_oneStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (valueCoreflexive : α) * (oneStepEvaluation a)∗ ≤ valueCoreflexive := by
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine LeanTra.Algebra.star_induction
    (a := oneStepEvaluation a)
    (x := (valueCoreflexive : α) ⇨ᵣ valueCoreflexive) ?_
  refine sup_le ?_ ?_
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    rw [mul_one]
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
    calc (valueCoreflexive : α)
            * (oneStepEvaluation a * ((valueCoreflexive : α) ⇨ᵣ valueCoreflexive))
        = ((valueCoreflexive : α) * oneStepEvaluation a)
            * ((valueCoreflexive : α) ⇨ᵣ valueCoreflexive) := by
          rw [mul_assoc]
      _ ≤ (valueCoreflexive : α)
            * ((valueCoreflexive : α) ⇨ᵣ valueCoreflexive) :=
          mul_le_mul' (valueCoreflexive_mul_oneStepEvaluation_le hgip) le_rfl
      _ ≤ (valueCoreflexive : α) :=
          Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl

/-- `Δ_κ * a^⇓ ≤ Δ_κ` — closedness is preserved by big-step evaluation.
Uses star-preservation + Δ̄'s coreflexivity. -/
theorem valueCoreflexive_mul_bigStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (valueCoreflexive : α) * bigStepEvaluation a ≤ valueCoreflexive := by
  change (valueCoreflexive : α) * ((oneStepEvaluation a)∗ * introductionCoreflexive)
    ≤ valueCoreflexive
  calc (valueCoreflexive : α) * ((oneStepEvaluation a)∗ * introductionCoreflexive)
      = ((valueCoreflexive : α) * (oneStepEvaluation a)∗) * introductionCoreflexive := by
        rw [mul_assoc]
    _ ≤ (valueCoreflexive : α) * introductionCoreflexive :=
        mul_le_mul' (valueCoreflexive_mul_star_oneStepEvaluation_le hgip) le_rfl
    _ ≤ (valueCoreflexive : α) * 1 :=
        mul_le_mul' le_rfl OperationalDecomposition.introduction_unit_oplaxity
    _ = valueCoreflexive := mul_one _

/-- `Δ̄ * a^⇓ ≤ Δ̄` under `GIP a`. Consequence of the previous lemma
via `bigStepEvaluation`'s definition. -/
theorem introductionCoreflexive_mul_bigStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) * bigStepEvaluation a ≤ introductionCoreflexive := by
  change (introductionCoreflexive : α) * ((oneStepEvaluation a)∗ * introductionCoreflexive)
    ≤ introductionCoreflexive
  calc (introductionCoreflexive : α) * ((oneStepEvaluation a)∗ * introductionCoreflexive)
      = ((introductionCoreflexive : α) * (oneStepEvaluation a)∗) * introductionCoreflexive := by
        rw [mul_assoc]
    _ ≤ (introductionCoreflexive : α) * introductionCoreflexive :=
        mul_le_mul' (introductionCoreflexive_mul_star_oneStepEvaluation_le hgip) le_rfl
    _ = introductionCoreflexive := introductionCoreflexive_mul_self



/-! ## Layer 2 — Proposition 29 and F1–F4 (draft's Fig. 7)

Fixed-point characterisation of `a^⇓`. From Lemma A.6 of the draft's
appendix: `a^⇓` is the least solution of `x = Δ_κ ∨ a * x ∨ ⟨x⟩ * x`
for closed rules. This gives four laws F1–F4:

* **F1** `Δ_κ ≤ a^⇓` — trivial from `Δ_κ ≤ Δ̄` and `Δ̄ ≤ a^⇓`.
* **F2** `a * a^⇓ ≤ a^⇓` — provable from `a ≤ a^E` and star absorption.
* **F3** `⟨a^⇓⟩ * a^⇓ ≤ a^⇓` — the substantive one, requires fixed-point
  induction. `sorry`.
* **F4** `Δ_κ ≤ b ∧ a * b ≤ b ∧ ⟨b⟩ * b ≤ b ⟹ a^⇓ ≤ b` — induction
  principle. Follows from Lemma A.6's LFP claim, not yet formalised.
  `sorry`. -/

/-- **F1**: `Δ_κ ≤ a^⇓`. The value coreflexive is contained in
big-step evaluation (values evaluate to themselves). Trivial from
`Δ_κ ≤ Δ̄` (`box_le`) and `Δ̄ ≤ a^⇓` (from `1 ≤ (a^E)∗`). -/
theorem valueCoreflexive_le_bigStepEvaluation {a : α} :
    (valueCoreflexive : α) ≤ bigStepEvaluation a := by
  calc (valueCoreflexive : α)
      ≤ introductionCoreflexive := SRA.box_le _
    _ = 1 * introductionCoreflexive := (one_mul _).symm
    _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (LeanTra.Algebra.star_reflexivity _) le_rfl

/-- **F2**: `a * a^⇓ ≤ a^⇓`. Any single reduction followed by big-step
is contained in big-step. Uses `a ≤ a^E` (from GIP) and Kleene star
absorption. -/
theorem rule_mul_bigStepEvaluation_le {a : α} (hgip : GIP a) :
    a * bigStepEvaluation a ≤ bigStepEvaluation a := by
  -- a ≤ a^E: by GIP a factors through an elimination with intro-major,
  -- and a^E's fixed point gives ⟨a^E⟩ * a ≤ a^E.
  have ha_le_aE : a ≤ oneStepEvaluation a := by
    calc a ≤ majorProjection introductionCoreflexive * a := hgip
      _ ≤ majorProjection (oneStepEvaluation a) * a := by
          refine mul_le_mul' (majorProjection_monotonicity ?_) le_rfl
          -- Δ̄ ≤ a^E from the fixed-point equation.
          calc (introductionCoreflexive : α)
              ≤ introductionCoreflexive ⊔
                  majorProjection (oneStepEvaluation a) * a := le_sup_left
            _ = oneStepEvaluation a := (oneStepEvaluation_fixpoint hgip).symm
      _ ≤ oneStepEvaluation a := by
          calc majorProjection (oneStepEvaluation a) * a
              ≤ introductionCoreflexive ⊔
                  majorProjection (oneStepEvaluation a) * a := le_sup_right
            _ = oneStepEvaluation a := (oneStepEvaluation_fixpoint hgip).symm
  -- a * a^⇓ = a * (a^E)∗ * Δ̄ ≤ a^E * (a^E)∗ * Δ̄ ≤ (a^E)∗ * Δ̄ = a^⇓.
  change a * ((oneStepEvaluation a)∗ * introductionCoreflexive)
    ≤ (oneStepEvaluation a)∗ * introductionCoreflexive
  calc a * ((oneStepEvaluation a)∗ * introductionCoreflexive)
      = a * (oneStepEvaluation a)∗ * introductionCoreflexive := by rw [mul_assoc]
    _ ≤ oneStepEvaluation a * (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (mul_le_mul' ha_le_aE le_rfl) le_rfl
    _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (LeanTra.Algebra.star_absorption_left _) le_rfl

/-- Prop 29 (equational form): `a^⇓ = Δ̄ ⊔ ⟨a^⇓⟩ * a * a^⇓`. Placed
here (before F3) so that F3 can use it. The `sorry` reflects that this
requires Lemma A.6 (the LFP characterisation) — the `(≤)` direction
via `bigStepEvaluation_unfold_le` uses `⟨a^E⟩`, and `a^E ≤ a^⇓` fails
in general (`a^E` need not end at a value), so bridging to `⟨a^⇓⟩`
demands the LFP framework. -/
theorem bigStepEvaluation_fixpoint {a : α} (_hgip : GIP a) :
    bigStepEvaluation a
      = (introductionCoreflexive : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a := by
  sorry

/-- Auxiliary: `a^⇓ * a^⇓ ≤ a^⇓`. Composing two big-step evaluations
gives a big-step evaluation. Direct from the definition: the trailing
`Δ̄` on the left absorbs the next `(a^E)∗` via
`Δ̄ * (a^E)∗ ≤ Δ̄`, and `Δ̄ * Δ̄ = Δ̄`. Used by F3. -/
theorem bigStepEvaluation_mul_self_le
    {a : α} (hgip : GIP a) :
    bigStepEvaluation a * bigStepEvaluation a ≤ bigStepEvaluation a := by
  change ((oneStepEvaluation a)∗ * introductionCoreflexive)
        * ((oneStepEvaluation a)∗ * introductionCoreflexive)
      ≤ (oneStepEvaluation a)∗ * introductionCoreflexive
  have key : (introductionCoreflexive : α) * (oneStepEvaluation a)∗
              * introductionCoreflexive
           ≤ (introductionCoreflexive : α) :=
    calc (introductionCoreflexive : α) * (oneStepEvaluation a)∗ * introductionCoreflexive
        ≤ (introductionCoreflexive : α) * introductionCoreflexive :=
          mul_le_mul' (introductionCoreflexive_mul_star_oneStepEvaluation_le hgip) le_rfl
      _ = introductionCoreflexive := introductionCoreflexive_mul_self
  calc ((oneStepEvaluation a)∗ * introductionCoreflexive)
          * ((oneStepEvaluation a)∗ * introductionCoreflexive)
      = (oneStepEvaluation a)∗
          * (introductionCoreflexive * (oneStepEvaluation a)∗
              * introductionCoreflexive) := by
        rw [mul_assoc, ← mul_assoc (introductionCoreflexive : α)]
    _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' le_rfl key

/-- **F3**: `⟨a^⇓⟩ * a^⇓ ≤ a^⇓`. If a term's major slot big-step
evaluates to a value, and the resulting elimination form big-step
evaluates, then the whole term big-step evaluates.

Proved from `bigStepEvaluation_fixpoint` (still `sorry`ed below): unfold
the right `a^⇓` via its fixed-point equation, kill the `⟨a^⇓⟩ * Δ̄`
summand by intro/elim orthogonality, and fold `⟨a^⇓⟩ * ⟨a^⇓⟩` into
`⟨a^⇓ * a^⇓⟩ ≤ ⟨a^⇓⟩` (by `majorProjection_compositionality` +
`bigStepEvaluation_mul_self_le`), landing back in the fixpoint's
elim-summand. -/
theorem majorProjection_bigStepEvaluation_mul_bigStepEvaluation_le
    {a : α} (hgip : GIP a) :
    majorProjection (bigStepEvaluation a) * bigStepEvaluation a
      ≤ bigStepEvaluation a := by
  have hfix := bigStepEvaluation_fixpoint hgip
  have hfold : majorProjection (bigStepEvaluation a * bigStepEvaluation a)
      ≤ majorProjection (bigStepEvaluation a) :=
    majorProjection_monotonicity (bigStepEvaluation_mul_self_le hgip)
  -- Substitute the right a^⇓ via the fixed-point equation, then bound.
  calc majorProjection (bigStepEvaluation a) * bigStepEvaluation a
      = majorProjection (bigStepEvaluation a)
          * ((introductionCoreflexive : α)
              ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a) :=
        congrArg (fun x => majorProjection (bigStepEvaluation a) * x) hfix
    _ = majorProjection (bigStepEvaluation a) * introductionCoreflexive
          ⊔ majorProjection (bigStepEvaluation a)
              * (majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a) :=
        Quantale.mul_sup_distrib
    _ ≤ (⊥ : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a := by
        refine sup_le_sup ?_ ?_
        · exact majorProjection_mul_introductionCoreflexive_le_bot _
        · calc majorProjection (bigStepEvaluation a)
                  * (majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a)
              = (majorProjection (bigStepEvaluation a)
                    * majorProjection (bigStepEvaluation a)) * a * bigStepEvaluation a := by
                rw [← mul_assoc, ← mul_assoc]
            _ = majorProjection (bigStepEvaluation a * bigStepEvaluation a)
                    * a * bigStepEvaluation a := by
                rw [majorProjection_compositionality]
            _ ≤ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a :=
                mul_le_mul' (mul_le_mul' hfold le_rfl) le_rfl
    _ = majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a :=
        bot_sup_eq _
    _ ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a :=
        le_sup_right
    _ = bigStepEvaluation a := hfix.symm

/-- **F4**: For a closed rule `a`, if `b` is closed under `Δ_κ`, `a * -`,
and `⟨-⟩ * -`, then `a^⇓ ≤ b`. Induction principle for `a^⇓`, from Lemma
A.6 of the draft's appendix (which characterises `a^⇓`, for closed `a`,
as the least solution of `x = Δ_κ ∨ a·x ∨ ⟨x⟩·x`).

Note: the closedness hypothesis on `a` is *essential*. Without it, the
statement is false: `Δ_κ ≤ b` does not entail `Δ̄ ≤ b`, yet
`a^⇓ = (a^E)∗ * Δ̄` starts (via `1 ≤ (a^E)∗`) with the full `Δ̄`
rather than `Δ_κ`. Closedness lets one sharpen `Δ̄` to `Δ_κ` inside
the reductive chain (Prop. 5.7 of the draft). -/
theorem bigStepEvaluation_induction {a b : α} (_hgip : GIP a) (_hcl : SRA.IsClosed a)
    (_hDκ : (valueCoreflexive : α) ≤ b)
    (_ha : a * b ≤ b)
    (_hproj : majorProjection b * b ≤ b) :
    bigStepEvaluation a ≤ b := by
  -- SORRY: F4 of Fig. 7. This is the LFP induction principle from
  -- Lemma A.6, which characterises `a^⇓`, for closed `a`, as the least
  -- solution of `x = Δ_κ ∨ a·x ∨ ⟨x⟩·x`. Its proof requires the
  -- equivalence between the operational definition
  -- `a^⇓ = (a^E)∗ * Δ̄` and the LFP characterisation, which itself
  -- goes through Prop. 5.7 of the draft (`□(a^E) = (□a)^E`) — an
  -- `IsClosedFun`-style transfer of `□` across the recursor's LFP
  -- (available in `SRA/Modality.lean` via `box_lfp`, but requiring
  -- the recursor to be a closed function). Estimated 80-120 lines
  -- once the closed-transfer machinery is set up.
  sorry

/-! ### Proposition 29

The paper's Prop 29 states `a^⇓` is the least solution of
`x = Δ̄ ∨ ⟨x⟩ * a * x` (general form) or `x = Δ_κ ∨ ⟨x⟩ * a * x`
(closed form). Both direction of the equality follow from F1-F4. -/

/-- **Proposition 29** of the paper (≤ direction). Under `GIP a`,
`a^⇓ ≤ Δ̄ ⊔ ⟨a^E⟩ * a * a^⇓`. The `⟨a^E⟩` slot inherits from the
elimination shape of `a^E`; strengthening it to `⟨a^⇓⟩` requires
the (≥)-direction of the same proposition, which is `sorry`ed below.
-/
theorem bigStepEvaluation_unfold_le {a : α} (hgip : GIP a) :
    bigStepEvaluation a
      ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
  -- Step 1: unfold a^⇓ once via the star's fixed-point equation.
  have hstep1 : bigStepEvaluation a
      = (introductionCoreflexive : α) ⊔ oneStepEvaluation a * bigStepEvaluation a := by
    change (oneStepEvaluation a)∗ * introductionCoreflexive
      = introductionCoreflexive ⊔ oneStepEvaluation a * ((oneStepEvaluation a)∗ * introductionCoreflexive)
    conv_lhs => rw [LeanTra.Algebra.star_fixpoint]
    rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]
  -- Step 2: expand a^E via its fixed-point equation and bound the pieces.
  have hstep2 : oneStepEvaluation a * bigStepEvaluation a
      ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
    conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
    rw [Quantale.sup_mul_distrib]
    refine sup_le ?_ le_sup_right
    exact (introductionCoreflexive_mul_bigStepEvaluation_le hgip).trans le_sup_left
  -- Combine: a^⇓ = Δ̄ ⊔ a^E * a^⇓ ≤ Δ̄ ⊔ (Δ̄ ⊔ ⟨a^E⟩ * a * a^⇓) = Δ̄ ⊔ ⟨a^E⟩ * a * a^⇓.
  calc bigStepEvaluation a
      = (introductionCoreflexive : α) ⊔ oneStepEvaluation a * bigStepEvaluation a := hstep1
    _ ≤ (introductionCoreflexive : α)
          ⊔ ((introductionCoreflexive : α)
              ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) :=
        sup_le_sup_left hstep2 _
    _ = (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
        rw [← sup_assoc, sup_idem]

/-- Proposition 29 (≥ direction): `Δ̄ ⊔ ⟨a^⇓⟩ * a * a^⇓ ≤ a^⇓`.
The `Δ̄` part is trivial (`1 ≤ (a^E)∗`); the elim-part collapses to
`⟨a^⇓⟩ * a^⇓` via F2 (`a * a^⇓ ≤ a^⇓`) and lands in `a^⇓` via F3.
Conditional on F3 (still `sorry`ed above). -/
theorem bigStepEvaluation_unfold_ge {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α)
        ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a
      ≤ bigStepEvaluation a := by
  refine sup_le ?_ ?_
  · -- Δ̄ = 1 * Δ̄ ≤ (a^E)∗ * Δ̄ = a^⇓.
    change (introductionCoreflexive : α)
      ≤ (oneStepEvaluation a)∗ * introductionCoreflexive
    calc (introductionCoreflexive : α)
        = 1 * introductionCoreflexive := (one_mul _).symm
      _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
          mul_le_mul' (LeanTra.Algebra.star_reflexivity _) le_rfl
  · -- ⟨a^⇓⟩ * a * a^⇓ ≤ ⟨a^⇓⟩ * a^⇓ ≤ a^⇓  (F2 then F3).
    calc majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a
        = majorProjection (bigStepEvaluation a) * (a * bigStepEvaluation a) := mul_assoc _ _ _
      _ ≤ majorProjection (bigStepEvaluation a) * bigStepEvaluation a :=
          mul_le_mul' le_rfl (rule_mul_bigStepEvaluation_le hgip)
      _ ≤ bigStepEvaluation a :=
          majorProjection_bigStepEvaluation_mul_bigStepEvaluation_le hgip

/-- Closed refinement of Proposition 29: for closed `a`,
`a^⇓ = Δ_κ ⊔ ⟨a^⇓⟩ * a * a^⇓`, i.e. Δ̄ can be sharpened to `Δ_κ`. -/
theorem bigStepEvaluation_fixpoint_closed {a : α}
    (_hgip : GIP a) (_hcl : SRA.IsClosed a) :
    bigStepEvaluation a
      = (valueCoreflexive : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a := by
  -- SORRY: builds on `bigStepEvaluation_fixpoint` (already sorry'd)
  -- and on Prop 29's second half `□(a^⇓) = (□a)^⇓`, whose proof
  -- requires `IsClosedFun` machinery from `SRA/Modality.lean`.
  sorry



/-! ## Layer 3 — The three intermediate steps -/

/-! ### Closed inversion principle -/

/-- **Closed inversion principle** (Def. A.7 in the draft's appendix):
`a = ⟨Δ_κ⟩ * a`, i.e. every `a`-step factors through an elimination
form whose major slot is a *value* (closed introduction form),
strengthening `GIP` (which only requires an introduction form). -/
def ClosedInversionPrinciple (a : α) : Prop :=
    a = majorProjection (valueCoreflexive : α) * a

/-! ### Step 1 — Inversion lemma

The correct statement (Prop. A.9 in the draft's appendix). Note the
trailing `* bigStepEvaluation a` on the right-hand side — earlier
mis-readings of the LICS'26 sketch dropped it, but without it the
inequality is algebraically false (LHS produces pairs (elim, intro),
RHS produces pairs (elim, elim), giving disjoint endpoints). -/

/-- **Inversion lemma** (Prop. A.9 of the draft's appendix). For any
rule `a` satisfying `GIP`, `⟨b⟩ * a^⇓ ≤ ⟨b * a^⇓⟩ * a^⇓`: a big-step
evaluation of an elimination form with major slot in `b` factors
through an intermediate stage in which the major slot has itself been
big-step evaluated, followed by a final big-step of the resulting
term.

The proof unfolds `a^⇓` via its fixed-point equation (Prop. 29),
kills the `⟨b⟩ * Δ̄` summand by intro/elim orthogonality, and folds
the remaining `⟨b⟩ * ⟨a^⇓⟩ * a * a^⇓` via `⟨_⟩` compositionality and
F2. Conditional on `bigStepEvaluation_fixpoint` (still `sorry`ed
above); needs neither closed inversion nor closedness of `a`. -/
theorem inversion_bigStep {a b : α} (hgip : GIP a)
    (_hinv : ClosedInversionPrinciple a) :
    majorProjection b * bigStepEvaluation a
      ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a := by
  -- Unfold a^⇓ once via its fixed-point equation:
  --   a^⇓ = Δ̄ ⊔ ⟨a^⇓⟩ * a * a^⇓.
  conv_lhs => rw [bigStepEvaluation_fixpoint hgip]
  rw [Quantale.mul_sup_distrib]
  refine sup_le ?_ ?_
  · -- ⟨b⟩ * Δ̄ ≤ ⊥ ≤ ⟨b * a^⇓⟩ * a^⇓.
    calc majorProjection b * (introductionCoreflexive : α)
        ≤ (⊥ : α) := majorProjection_mul_introductionCoreflexive_le_bot _
      _ ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a :=
          bot_le
  · -- ⟨b⟩ * (⟨a^⇓⟩ * a * a^⇓)
    --   = ⟨b * a^⇓⟩ * a * a^⇓  (⟨_⟩ compositionality)
    --   ≤ ⟨b * a^⇓⟩ * a^⇓      (F2 on the trailing a * a^⇓).
    calc majorProjection b
            * (majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a)
        = (majorProjection b * majorProjection (bigStepEvaluation a))
            * a * bigStepEvaluation a := by
          rw [← mul_assoc, ← mul_assoc]
      _ = majorProjection (b * bigStepEvaluation a) * a * bigStepEvaluation a := by
          rw [majorProjection_compositionality]
      _ = majorProjection (b * bigStepEvaluation a) * (a * bigStepEvaluation a) := by
          rw [mul_assoc]
      _ ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a :=
          mul_le_mul' le_rfl (rule_mul_bigStepEvaluation_le hgip)

/-! ### Step 2 — Determinism at the reduction level

Following Thm. A.12's proof in the draft's appendix. **Note on the
determinism assumption**: the appendix's Theorem statement writes
`a ; a° ≤ Δ`, but the actual calculational proof and the walkthrough
example on p. 3 both use `a° ; a ≤ Δ` (forward determinism, matching
this file's `LeanTra.Confluence.IsDeterministic`). We use the latter,
which is the assumption β actually satisfies.

Proof outline: from `a = ⟨Δ_κ⟩ * a` we get by converse
`aᵒ = aᵒ * ⟨Δ_κ⟩`. Then:
`aᵒ * a^⇓ = aᵒ * ⟨Δ_κ⟩ * a^⇓ ≤ aᵒ * a * a^⇓ ≤ a^⇓`
where the middle step uses the inversion lemma + Prop 29's closed
form (`Δ_κ * a^⇓ ≤ Δ_κ` for closed a), and the last step uses
forward determinism `aᵒ * a ≤ Δ`. -/

/-- Under forward determinism `aᵒ * a ≤ Δ` (together with the closed
inversion principle and `GIP a`), `aᵒ` is absorbed by the big-step
evaluation of `a` on the left: `aᵒ * a^⇓ ≤ a^⇓`. Thm. A.12 (part 1)
of the draft's appendix. -/
theorem opp_bigStep_le_bigStep {a : α} (hgip : GIP a)
    (hinv : ClosedInversionPrinciple a) (hdet : aᵒ * a ≤ 1) :
    aᵒ * bigStepEvaluation a ≤ bigStepEvaluation a := by
  -- Involution of the closed inversion principle: aᵒ = aᵒ * ⟨Δ_κ⟩.
  have hinv_op : aᵒ = aᵒ * majorProjection (valueCoreflexive : α) := by
    have hc := congrArg IsInvolutiveQuantale.converse hinv
    rw [IsInvolutiveQuantale.converse_compositionality] at hc
    have hcp : (majorProjection (valueCoreflexive : α))ᵒ
             = majorProjection (valueCoreflexive : α) := by
      rw [majorProjection_converse]
      congr 1
      change (□ introductionCoreflexive)ᵒ = □ introductionCoreflexive
      rw [SRA.box_converse_commutation]
      congr 1
      exact introductionCoreflexive_converse
    rw [hcp] at hc
    exact hc
  -- Sub-lemma: Δ_κ * a^E ≤ Δ_κ. From `a^E = Δ̄ ⊔ ⟨a^E⟩ * a`, both
  -- summands land in Δ_κ or are killed by intro/elim orthogonality.
  have hDκ_aE : (valueCoreflexive : α) * oneStepEvaluation a ≤ valueCoreflexive := by
    conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
    rw [Quantale.mul_sup_distrib]
    refine sup_le ?_ ?_
    · -- Δ_κ * Δ̄ ≤ Δ_κ (since Δ̄ ≤ 1)
      calc (valueCoreflexive : α) * introductionCoreflexive
          ≤ (valueCoreflexive : α) * 1 := by
            refine mul_le_mul' le_rfl ?_
            change OperationalDecomposition.introduction 1 ≤ 1
            exact OperationalDecomposition.introduction_unit_oplaxity
        _ = valueCoreflexive := mul_one _
    · -- Δ_κ * ⟨a^E⟩ * a ≤ intro 1 * elim a^E 1 * a ≤ ⊥
      have hDκ_le_intro : (valueCoreflexive : α) ≤ OperationalDecomposition.introduction 1 := by
        change □ (OperationalDecomposition.introduction 1) ≤ OperationalDecomposition.introduction 1
        exact SRA.box_le _
      calc (valueCoreflexive : α) * (majorProjection (oneStepEvaluation a) * a)
          = ((valueCoreflexive : α) * majorProjection (oneStepEvaluation a)) * a := by
            rw [mul_assoc]
        _ ≤ (OperationalDecomposition.introduction 1
              * OperationalDecomposition.elimination (oneStepEvaluation a) 1) * a := by
            refine mul_le_mul' ?_ le_rfl
            change (valueCoreflexive : α) * OperationalDecomposition.elimination (oneStepEvaluation a) 1
                 ≤ OperationalDecomposition.introduction 1
                    * OperationalDecomposition.elimination (oneStepEvaluation a) 1
            exact mul_le_mul' hDκ_le_intro le_rfl
        _ ≤ (⊥ : α) * a := by
            refine mul_le_mul' ?_ le_rfl
            exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
        _ = ⊥ := Quantale.bot_mul
        _ ≤ valueCoreflexive := bot_le
  -- Key sub-goal: ⟨Δ_κ⟩ * a^⇓ ≤ a * a^⇓. Uses `bigStepEvaluation_unfold_le`
  -- to split a^⇓, then orthogonality on the Δ̄ arm and Inv on the ⟨a^E⟩ arm.
  have hkey : majorProjection (valueCoreflexive : α) * bigStepEvaluation a
            ≤ a * bigStepEvaluation a := by
    have hunfold := bigStepEvaluation_unfold_le (a := a) hgip
    calc majorProjection (valueCoreflexive : α) * bigStepEvaluation a
        ≤ majorProjection (valueCoreflexive : α)
            * ((introductionCoreflexive : α)
                ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) :=
          mul_le_mul' le_rfl hunfold
      _ = majorProjection (valueCoreflexive : α) * introductionCoreflexive
            ⊔ majorProjection (valueCoreflexive : α)
                * (majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) := by
          rw [Quantale.mul_sup_distrib]
      _ ≤ (⊥ : α) ⊔ a * bigStepEvaluation a := by
          refine sup_le_sup ?_ ?_
          · exact majorProjection_mul_introductionCoreflexive_le_bot _
          · calc majorProjection (valueCoreflexive : α)
                    * (majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a)
                = (majorProjection (valueCoreflexive : α)
                    * majorProjection (oneStepEvaluation a)) * a * bigStepEvaluation a := by
                  rw [← mul_assoc, ← mul_assoc]
              _ = majorProjection ((valueCoreflexive : α) * oneStepEvaluation a) * a
                    * bigStepEvaluation a := by
                  rw [majorProjection_compositionality]
              _ ≤ majorProjection (valueCoreflexive : α) * a * bigStepEvaluation a := by
                  refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
                  exact majorProjection_monotonicity hDκ_aE
              _ = a * bigStepEvaluation a := by
                  rw [← hinv]
      _ = a * bigStepEvaluation a := by rw [bot_sup_eq]
  -- Final calc.
  calc aᵒ * bigStepEvaluation a
      = aᵒ * majorProjection (valueCoreflexive : α) * bigStepEvaluation a := by
        rw [← hinv_op]
    _ = aᵒ * (majorProjection (valueCoreflexive : α) * bigStepEvaluation a) := by
        rw [mul_assoc]
    _ ≤ aᵒ * (a * bigStepEvaluation a) := mul_le_mul' le_rfl hkey
    _ = (aᵒ * a) * bigStepEvaluation a := (mul_assoc _ _ _).symm
    _ ≤ 1 * bigStepEvaluation a := mul_le_mul' hdet le_rfl
    _ = bigStepEvaluation a := one_mul _

/-! ### Step 3 — Value coreflexive as fixed point -/

/-- For a closed reduction `a` satisfying `aᵒ * a^⇓ ≤ a^⇓`, big-step
evaluation is deterministic up to the value coreflexive:
`(a^⇓)ᵒ * a^⇓ ≤ Δ_κ`. The proof is an algebraic manipulation on the
fixed-point equation `a^⇓ = Δ_κ ⊔ ⟨a^⇓⟩ * a * a^⇓` (Proposition 29's
closed refinement). -/
theorem bigStep_op_bigStep_le_valueCoreflexive
    {a : α}
    (_hcl : SRA.IsClosed a) (_hred : LeanTra.Confluence.IsReduction a)
    (_habs : aᵒ * bigStepEvaluation a ≤ bigStepEvaluation a) :
    (bigStepEvaluation a)ᵒ * bigStepEvaluation a
      ≤ valueCoreflexive := by
  -- SORRY: consumes `bigStepEvaluation_fixpoint_closed` (Layer 2).
  -- The proof expands both `(a^⇓)ᵒ` and `a^⇓` via the closed
  -- fixed-point equation, applies orthogonality to kill three of
  -- the four cross-terms, and uses `habs` to fold the residual
  -- back into Δ_κ. Estimated 30–60 lines.
  sorry



/-! ## Layer 4 — The main theorem -/

/-- **Determinism of big-step evaluation** (Theorem A.12 of the
draft's appendix / Theorem 31 of the LICS'26 paper). Let `a` be a
closed reduction satisfying `GIP` and the closed inversion principle.
If `a` is backward-deterministic (`a * aᵒ ≤ Δ`), then `a^⇓` is
deterministic up to the value coreflexive. -/
theorem determinism {a : α}
    (hcl : SRA.IsClosed a) (hred : LeanTra.Confluence.IsReduction a)
    (hinv : ClosedInversionPrinciple a) (hdet : aᵒ * a ≤ 1) (hgip : GIP a) :
    (bigStepEvaluation a)ᵒ * bigStepEvaluation a ≤ valueCoreflexive :=
  bigStep_op_bigStep_le_valueCoreflexive hcl hred
    (opp_bigStep_le_bigStep hgip hinv hdet)

end LeanTra.Metatheory

#check @LeanTra.Metatheory.determinism
#print axioms LeanTra.Metatheory.determinism
#print axioms LeanTra.Metatheory.opp_bigStep_le_bigStep
