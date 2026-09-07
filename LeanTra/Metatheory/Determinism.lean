/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Evaluation
public import LeanTra.Algebra.Diamond

/-!
# Determinism of big-step evaluation

A rule of computation is deterministic when any two of its rewrites of
the same term agree, `aᵒ * a ≤ Δ`. The theorem of this file says that
determinism survives the passage to big-step semantics: if `a` is
deterministic and satisfies Gentzen's inversion principle, then its
big-step evaluation relates every term to at most one canonical form,
`(a^⇓)ᵒ * a^⇓ ≤ Δ̄`. Read relationally, the left-hand side relates any
two outcomes of evaluating a common source, and the right-hand side
says that they are one and the same introduction form. Nothing else is
assumed: no closedness of the rule, no compatibility, no strengthening
of inversion to values.

The bound is the introduction coreflexive and not the value
coreflexive, and necessarily so. An introduction form evaluates to
itself in zero steps, `Δ̄ ≤ a^⇓`, hence
`Δ̄ = Δ̄ᵒ * Δ̄ ≤ (a^⇓)ᵒ * a^⇓`: a bound at the values would force
every introduction form to be closed, which fails in any model with
open terms.

`Metatheory/Evaluation.lean` supplies the definitions of
`oneStepEvaluation`, `bigStepEvaluation`, and their fixed-point
equations and induction principles. Everything else the theorem needs
about evaluation — the inertness of introduction forms under a run, the
unfolding of a big-step run, the fusion of the leading firing back into
the run, and the compound induction principle on `a^⇓` — is proved
locally in this file, as private lemmas above `determinism`. The
theorem itself is then a three-stage argument, marked by the
separators inside its proof:

* **The rule reversed is absorbed by evaluation.** The converse of
  inversion gives `aᵒ ≤ aᵒ * ⟨Δ̄⟩`; an elimination form whose major
  argument is already canonical can only fire,
  `⟨Δ̄⟩ * a^⇓ ≤ a * a^⇓`; and determinism collapses the resulting
  `aᵒ * a` into the identity. Together: `aᵒ * a^⇓ ≤ a^⇓`.
* **Inversion for big-step runs.** For every `b`,
  `⟨b⟩ * a^⇓ ≤ ⟨b * a^⇓⟩ * a^⇓`: a run from an elimination form first
  evaluates the major argument, then continues from the result. From
  one unfolding of the run, orthogonality and the fusion of major
  projections.
* **Uniqueness of the reached canonical form.** The two stages
  discharge the hypotheses of the converse induction principle at the
  residual `c := a^⇓ ⇨ₗ Δ̄`, the largest relation whose composition
  with `a^⇓` lands in `Δ̄`. The principle yields `(a^⇓)ᵒ ≤ c`, which
  transposes to the theorem.

## Two departures from the reference

The reference establishes this result through appendix statements that
are slightly stronger than its definitions allow; both must be
weakened, and the corrections propagate to the forms proved in this
development.

First, the reference's Theorem 31 concludes at the values,
`(a^⇓)ᵒ * a^⇓ ≤ Δ_κ`. By the observation above this entails
`Δ̄ ≤ Δ_κ`, which is refutable whenever an open canonical form exists.
The conclusion proved here is the `Δ̄` of the walkthrough theorem (†)
of the reference's introduction. For the same reason, the base
hypothesis of the induction principle for `a^⇓` (the reference's F4)
must sit at `Δ̄` rather than `Δ_κ`.

Second, the reference's Proposition 29 characterises `a^⇓` as a least
fixed point; only the `(≤)` direction of that equation holds, and it
is the only direction used here. Concretely: one `a^E`-step fires the
rule at most once per level of the major spine, whereas the right-hand
side of the fixed-point equation may fire twice at the same level (in
the λ-calculus, `app(I(II), s)` with `I = λx.x` admits no `a^E`-step
at all, yet the right-hand side relates it to a value).

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System
  Metatheory.* LICS 2026, Theorem 31.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale
open LeanTra.Algebra
open OperationalDecomposition

namespace LeanTra.Metatheory

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

/-! ### Introduction forms are inert

Under `GIP` a rule fires only through an elimination form, so an
introduction form offers it nothing: one step of evaluation returns the
same introduction form, and iterating changes nothing. Together with
`Δ̄ ≤ a^E` and `a ≤ a^E`, these absorption laws are the elementary facts
the rest of the file runs on. -/

/-- `Δ̄ ≤ a^E`: a term in constructed shape is an answer, so one step of
evaluation may return it unchanged. Immediate from the fixed-point
equation. -/
private theorem introductionCoreflexive_le_oneStepEvaluation {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) ≤ oneStepEvaluation a :=
  le_sup_left.trans (oneStepEvaluation_fixpoint hgip).ge

/-- `a ≤ a^E`: a single firing of the rule is one step of evaluation.
By inversion the inspected argument of a firing already holds a
constructor, so no descent is needed before the rule acts. -/
private theorem rule_le_oneStepEvaluation {a : α} (hgip : GIP a) :
    a ≤ oneStepEvaluation a :=
  calc a ≤ majorProjection introductionCoreflexive * a := hgip
    _ ≤ majorProjection (oneStepEvaluation a) * a :=
        mul_le_mul'
          (majorProjection_monotonicity
            (introductionCoreflexive_le_oneStepEvaluation hgip))
          le_rfl
    _ ≤ oneStepEvaluation a :=
        le_sup_right.trans (oneStepEvaluation_fixpoint hgip).ge

/-- `Δ̄ * a^E ≤ Δ̄`: starting at an introduction form, one step of
evaluation gives back that same introduction form. The firing summand of
`a^E` dies against intro/elim orthogonality. -/
private theorem introductionCoreflexive_mul_oneStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) * oneStepEvaluation a ≤ introductionCoreflexive := by
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

/-- `Δ̄ * (a^E)∗ ≤ Δ̄`: iterating changes nothing either. Kleene-star
induction on the previous law, run through the right residual. -/
private theorem introductionCoreflexive_mul_star_oneStepEvaluation_le
    {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) * (oneStepEvaluation a)∗ ≤ introductionCoreflexive := by
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
            * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive) := by
          exact mul_le_mul' (introductionCoreflexive_mul_oneStepEvaluation_le hgip) le_rfl
      _ ≤ (introductionCoreflexive : α) :=
          Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl

/-- `Δ̄ * a^⇓ ≤ Δ̄`: a big-step run starting at an introduction form
never leaves it. -/
private theorem introductionCoreflexive_mul_bigStepEvaluation_le
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

/-! ### Basic laws of big-step evaluation

An introduction form evaluates to itself, and prefixing a firing to a
big-step run gives a big-step run. -/

/-- `Δ̄ ≤ a^⇓`: an introduction form evaluates to itself, in zero
one-step evaluations. Holds for every rule; in particular any relation
containing `(a^⇓)ᵒ * a^⇓` contains the whole of `Δ̄`. -/
private theorem introductionCoreflexive_le_bigStepEvaluation {a : α} :
    (introductionCoreflexive : α) ≤ bigStepEvaluation a :=
  calc (introductionCoreflexive : α)
      = 1 * introductionCoreflexive := (one_mul _).symm
    _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (LeanTra.Algebra.star_reflexivity _) le_rfl

/-- `a * a^⇓ ≤ a^⇓`: firing the rule and then evaluating is
evaluating. From `a ≤ a^E` and star absorption. -/
private theorem rule_mul_bigStepEvaluation_le {a : α} (hgip : GIP a) :
    a * bigStepEvaluation a ≤ bigStepEvaluation a := by
  change a * ((oneStepEvaluation a)∗ * introductionCoreflexive)
    ≤ (oneStepEvaluation a)∗ * introductionCoreflexive
  calc a * ((oneStepEvaluation a)∗ * introductionCoreflexive)
      = a * (oneStepEvaluation a)∗ * introductionCoreflexive := by rw [mul_assoc]
    _ ≤ oneStepEvaluation a * (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (mul_le_mul' (rule_le_oneStepEvaluation hgip) le_rfl) le_rfl
    _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (LeanTra.Algebra.star_absorption_left _) le_rfl

/-! ### Unfolding a big-step run

A big-step run is either at rest or one firing under an evaluated major
argument: `a^⇓ ≤ Δ̄ ⊔ ⟨a^⇓⟩ * a * a^⇓`. This is an inequality, not an
equation — see the module docstring for the failing direction and the
concrete counterexample. -/

/-- One unfolding of a big-step run, with the one-step evaluation in the
major slot: `a^⇓ ≤ Δ̄ ⊔ ⟨a^E⟩ * a * a^⇓`. The slot inherits from the
fixed-point equation of `a^E`; `bigStepEvaluation_unfold` upgrades it
to `⟨a^⇓⟩`. -/
private theorem bigStepEvaluation_unfold_le {a : α} (hgip : GIP a) :
    bigStepEvaluation a
      ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
  -- Unfold `a^⇓` once via the star's fixed-point equation.
  have hstep1 : bigStepEvaluation a
      = (introductionCoreflexive : α) ⊔ oneStepEvaluation a * bigStepEvaluation a := by
    change (oneStepEvaluation a)∗ * introductionCoreflexive
      = introductionCoreflexive ⊔ oneStepEvaluation a * ((oneStepEvaluation a)∗ * introductionCoreflexive)
    conv_lhs => rw [LeanTra.Algebra.star_fixpoint]
    rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]
  -- Expand `a^E` via its fixed-point equation and bound the pieces.
  have hstep2 : oneStepEvaluation a * bigStepEvaluation a
      ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
    conv_lhs => rw [oneStepEvaluation_fixpoint hgip]
    rw [Quantale.sup_mul_distrib]
    refine sup_le ?_ le_sup_right
    exact (introductionCoreflexive_mul_bigStepEvaluation_le hgip).trans le_sup_left
  calc bigStepEvaluation a
      = (introductionCoreflexive : α) ⊔ oneStepEvaluation a * bigStepEvaluation a := hstep1
    _ ≤ (introductionCoreflexive : α)
          ⊔ ((introductionCoreflexive : α)
              ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) :=
        sup_le_sup_left hstep2 _
    _ = (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a := by
        rw [← sup_assoc, sup_idem]

/-- One unfolding of a big-step run, with the big-step evaluation in the
major slot: `a^⇓ ≤ Δ̄ ⊔ ⟨a^⇓⟩ * a * a^⇓`. By inversion, `a` factors as
`⟨Δ̄⟩ * a`, so the slot of `bigStepEvaluation_unfold_le` fuses to
`⟨a^E * Δ̄⟩`, and a one-step run ending at an introduction form is a
big-step run. -/
private theorem bigStepEvaluation_unfold {a : α} (hgip : GIP a) :
    bigStepEvaluation a
      ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a := by
  have hslot : majorProjection (oneStepEvaluation a) * a
      ≤ majorProjection (bigStepEvaluation a) * a := by
    calc majorProjection (oneStepEvaluation a) * a
        ≤ majorProjection (oneStepEvaluation a)
            * (majorProjection (introductionCoreflexive : α) * a) :=
          mul_le_mul' le_rfl hgip
      _ = (majorProjection (oneStepEvaluation a)
            * majorProjection (introductionCoreflexive : α)) * a := by
          rw [← mul_assoc]
      _ = majorProjection (oneStepEvaluation a * introductionCoreflexive) * a := by
          rw [majorProjection_compositionality]
      _ ≤ majorProjection (bigStepEvaluation a) * a := by
          refine mul_le_mul' (majorProjection_monotonicity ?_) le_rfl
          change oneStepEvaluation a * introductionCoreflexive
            ≤ (oneStepEvaluation a)∗ * introductionCoreflexive
          exact mul_le_mul' (LeanTra.Algebra.star_extensivity _) le_rfl
  calc bigStepEvaluation a
      ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a :=
        bigStepEvaluation_unfold_le hgip
    _ ≤ (introductionCoreflexive : α)
          ⊔ majorProjection (bigStepEvaluation a) * a * bigStepEvaluation a :=
        sup_le_sup_left (mul_le_mul' hslot le_rfl) _

/-! ### Induction principles

`a^⇓` is built from two least fixed points — the recursor of `a^E` and
the Kleene star — and the two combine into a single induction principle:
anything containing `Δ̄` and closed under `a * ·` and `⟨·⟩ * ·` contains
`a^⇓`. Both inductions are run through the left residual `b ⇨ₗ b`, the
largest relation whose composition with `b` stays inside `b`. The
converse mirror follows by involution alone. -/

/-- Induction on big-step runs: if `b` contains `Δ̄` and is closed under
`a * ·` and `⟨·⟩ * ·`, then `a^⇓ ≤ b`.

The hypothesis at `Δ̄` cannot be weakened to the values: `Δ̄ ≤ a^⇓`
holds for every rule, so every upper bound of `a^⇓` must already
contain the whole of `Δ̄`.

The proof runs the fixed-point induction of `a^E` and the Kleene-star
induction through the left residual `b ⇨ₗ b`. Three observations close
the inductive step: `Δ̄ ≤ Δ`; inversion inserts `⟨Δ̄⟩` in front of `a`,
which fuses with `⟨b ⇨ₗ b⟩` into `⟨(b ⇨ₗ b) * Δ̄⟩ ≤ ⟨b⟩`; and the two
closure hypotheses then absorb `⟨b⟩ * a * b`. -/
private theorem bigStepEvaluation_induction {a b : α} (hgip : GIP a)
    (hD : (introductionCoreflexive : α) ≤ b)
    (ha : a * b ≤ b)
    (hproj : majorProjection b * b ≤ b) :
    bigStepEvaluation a ≤ b := by
  -- a^E ≤ b ⇨ₗ b, by the fixed-point induction of one-step evaluation.
  have haE : oneStepEvaluation a ≤ b ⇨ₗ b := by
    refine oneStepEvaluation_induction hgip (sup_le ?_ ?_)
    · -- Δ̄ * b ≤ b, since Δ̄ ≤ 1.
      refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      calc (introductionCoreflexive : α) * b
          ≤ 1 * b :=
            mul_le_mul' OperationalDecomposition.introduction_unit_oplaxity le_rfl
        _ = b := one_mul b
    · -- ⟨b ⇨ₗ b⟩ * a * b ≤ b.
      refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      -- (b ⇨ₗ b) * Δ̄ ≤ b, via Δ̄ ≤ b and the residuation law.
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
  -- (a^E)∗ ≤ b ⇨ₗ b, by Kleene-star induction.
  have hstar : (oneStepEvaluation a)∗ ≤ b ⇨ₗ b := by
    refine LeanTra.Algebra.star_induction (sup_le ?_ ?_)
    · exact Quantale.leftMulResiduation_le_iff_mul_le.mpr (by rw [one_mul])
    · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      calc oneStepEvaluation a * (b ⇨ₗ b) * b
          = oneStepEvaluation a * ((b ⇨ₗ b) * b) := mul_assoc _ _ _
        _ ≤ oneStepEvaluation a * b :=
            mul_le_mul' le_rfl (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl)
        _ ≤ b := Quantale.leftMulResiduation_le_iff_mul_le.mp haE
  -- Conclude: a^⇓ = (a^E)∗ * Δ̄ ≤ (b ⇨ₗ b) * b ≤ b.
  change (oneStepEvaluation a)∗ * introductionCoreflexive ≤ b
  calc (oneStepEvaluation a)∗ * (introductionCoreflexive : α)
      ≤ (b ⇨ₗ b) * (introductionCoreflexive : α) := mul_le_mul' hstar le_rfl
    _ ≤ (b ⇨ₗ b) * b := mul_le_mul' le_rfl hD
    _ ≤ b := Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl

/-- Converse mirror of `bigStepEvaluation_induction`: if `b` contains
`Δ̄` and is closed under `· * aᵒ` and `· * ⟨·⟩`, then `(a^⇓)ᵒ ≤ b`.
Apply the forward principle to `bᵒ` and transport every hypothesis
through the involution. -/
private theorem bigStepEvaluation_induction_op {a b : α} (hgip : GIP a)
    (hD : (introductionCoreflexive : α) ≤ b)
    (ha : b * aᵒ ≤ b)
    (hproj : b * majorProjection b ≤ b) :
    (bigStepEvaluation a)ᵒ ≤ b := by
  have h : bigStepEvaluation a ≤ bᵒ := by
    refine bigStepEvaluation_induction hgip ?_ ?_ ?_
    · -- Δ̄ ≤ bᵒ, since Δ̄ is self-converse.
      rw [← introductionCoreflexive_converse]
      exact IsInvolutiveQuantale.converse_monotonicity hD
    · -- a * bᵒ ≤ bᵒ, the converse of `b * aᵒ ≤ b`.
      have h' := IsInvolutiveQuantale.converse_monotonicity ha
      rwa [IsInvolutiveQuantale.converse_compositionality,
          IsInvolutiveQuantale.converse_involutivity] at h'
    · -- ⟨bᵒ⟩ * bᵒ ≤ bᵒ, the converse of `b * ⟨b⟩ ≤ b`.
      have h' := IsInvolutiveQuantale.converse_monotonicity hproj
      rwa [IsInvolutiveQuantale.converse_compositionality,
          majorProjection_converse] at h'
  have h' := IsInvolutiveQuantale.converse_monotonicity h
  rwa [IsInvolutiveQuantale.converse_involutivity] at h'

/-! ### The theorem -/

/-- **Determinism of big-step evaluation**: for a deterministic rule
satisfying Gentzen's inversion principle, big-step evaluation relates
every term to at most one canonical form, `(a^⇓)ᵒ * a^⇓ ≤ Δ̄`. -/
theorem determinism {a : α}
    (hgip : GIP a)
    (hdet : IsDeterministic a) :
    (bigStepEvaluation a)ᵒ * bigStepEvaluation a ≤ introductionCoreflexive := by
  -- The rule reversed is absorbed by evaluation
  --
  -- `aᵒ * a^⇓ ≤ a^⇓`. The converse of inversion writes `aᵒ` as
  -- `aᵒ * ⟨Δ̄⟩`; the unfolding of a big-step run shows that an
  -- elimination form whose major argument is already canonical can only
  -- fire, `⟨Δ̄⟩ * a^⇓ ≤ a * a^⇓`; and determinism collapses the
  -- resulting `aᵒ * a` into the identity.
  have habs : aᵒ * bigStepEvaluation a ≤ bigStepEvaluation a := by
    have hgip_op : aᵒ ≤ aᵒ * majorProjection (introductionCoreflexive : α) := by
      have h := IsInvolutiveQuantale.converse_monotonicity hgip
      rwa [IsInvolutiveQuantale.converse_compositionality, majorProjection_converse,
          introductionCoreflexive_converse] at h
    have hkey : majorProjection (introductionCoreflexive : α) * bigStepEvaluation a
              ≤ a * bigStepEvaluation a := by
      calc majorProjection (introductionCoreflexive : α) * bigStepEvaluation a
          ≤ majorProjection (introductionCoreflexive : α)
              * ((introductionCoreflexive : α)
                  ⊔ majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) :=
            mul_le_mul' le_rfl (bigStepEvaluation_unfold_le hgip)
        _ = majorProjection (introductionCoreflexive : α) * introductionCoreflexive
              ⊔ majorProjection (introductionCoreflexive : α)
                  * (majorProjection (oneStepEvaluation a) * a * bigStepEvaluation a) := by
            rw [Quantale.mul_sup_distrib]
        _ ≤ (⊥ : α) ⊔ a * bigStepEvaluation a := by
            refine sup_le_sup ?_ ?_
            · exact majorProjection_mul_introductionCoreflexive_le_bot _
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
                    exact majorProjection_monotonicity
                      (introductionCoreflexive_mul_oneStepEvaluation_le hgip)
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
  -- `⟨b⟩ * a^⇓ ≤ ⟨b * a^⇓⟩ * a^⇓` for every `b`. Unfold the run once:
  -- the resting summand `⟨b⟩ * Δ̄` dies against intro/elim
  -- orthogonality, and on the firing summand the two major projections
  -- fuse, after which the leading firing is reabsorbed into the run.
  have hinv : ∀ b : α, majorProjection b * bigStepEvaluation a
      ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a := by
    intro b
    refine le_trans (mul_le_mul' le_rfl (bigStepEvaluation_unfold hgip)) ?_
    rw [Quantale.mul_sup_distrib]
    refine sup_le ?_ ?_
    · calc majorProjection b * (introductionCoreflexive : α)
          ≤ (⊥ : α) := majorProjection_mul_introductionCoreflexive_le_bot _
        _ ≤ majorProjection (b * bigStepEvaluation a) * bigStepEvaluation a :=
            bot_le
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
            mul_le_mul' le_rfl (rule_mul_bigStepEvaluation_le hgip)
  -- Uniqueness of the reached canonical form
  --
  -- Work at the residual `c := a^⇓ ⇨ₗ Δ̄`, so that `z ≤ c` iff
  -- `z * a^⇓ ≤ Δ̄`; `hc` is its counit. The converse induction
  -- principle applied at `c` needs `Δ̄ ≤ c` (the absorption law of
  -- introduction forms), `c * aᵒ ≤ c` (the first stage) and
  -- `c * ⟨c⟩ ≤ c` (the second stage, with the fused slot collapsing
  -- through `⟨Δ̄⟩ ≤ Δ`). It yields `(a^⇓)ᵒ ≤ c`, and transposing back
  -- along the residual is the theorem.
  have hc : (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
      * bigStepEvaluation a ≤ introductionCoreflexive :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hmain : (bigStepEvaluation a)ᵒ
      ≤ bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α) := by
    refine bigStepEvaluation_induction_op hgip ?_ ?_ ?_
    · -- Δ̄ ≤ c, i.e. Δ̄ * a^⇓ ≤ Δ̄.
      exact Quantale.leftMulResiduation_le_iff_mul_le.mpr
        (introductionCoreflexive_mul_bigStepEvaluation_le hgip)
    · -- c * aᵒ ≤ c: c * aᵒ * a^⇓ ≤ c * a^⇓ ≤ Δ̄, by the first stage.
      refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      calc (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α)) * aᵒ
              * bigStepEvaluation a
          = (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * (aᵒ * bigStepEvaluation a) := mul_assoc _ _ _
        _ ≤ (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * bigStepEvaluation a := mul_le_mul' le_rfl habs
        _ ≤ introductionCoreflexive := hc
    · -- c * ⟨c⟩ ≤ c: by the second stage, ⟨c⟩ * a^⇓ factors through
      -- ⟨c * a^⇓⟩ * a^⇓ ≤ ⟨Δ̄⟩ * a^⇓ ≤ a^⇓, and c absorbs a^⇓ into Δ̄.
      refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
      have hproj : majorProjection
            (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
            * bigStepEvaluation a
          ≤ bigStepEvaluation a :=
        calc majorProjection
              (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * bigStepEvaluation a
            ≤ majorProjection
                ((bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
                  * bigStepEvaluation a)
                * bigStepEvaluation a := hinv _
          _ ≤ majorProjection (introductionCoreflexive : α) * bigStepEvaluation a :=
              mul_le_mul' (majorProjection_monotonicity hc) le_rfl
          _ ≤ 1 * bigStepEvaluation a :=
              mul_le_mul' majorProjection_introductionCoreflexive_le_one le_rfl
          _ = bigStepEvaluation a := one_mul _
      calc (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * majorProjection
                  (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * bigStepEvaluation a
          = (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * (majorProjection
                  (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
                  * bigStepEvaluation a) := mul_assoc _ _ _
        _ ≤ (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
              * bigStepEvaluation a := mul_le_mul' le_rfl hproj
        _ ≤ introductionCoreflexive := hc
  calc (bigStepEvaluation a)ᵒ * bigStepEvaluation a
      ≤ (bigStepEvaluation a ⇨ₗ (introductionCoreflexive : α))
          * bigStepEvaluation a := mul_le_mul' hmain le_rfl
    _ ≤ introductionCoreflexive := hc

end LeanTra.Metatheory

#check @LeanTra.Metatheory.determinism
#print axioms LeanTra.Metatheory.determinism
