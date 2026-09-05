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

The whole argument is the single theorem `determinism`. Everything it
consumes about evaluation — the absorption laws, the unfolding of a
big-step run, and the converse induction principle — is supplied by
`Metatheory/Evaluation.lean`; the hypothesis `IsDeterministic` lives in
`Algebra/Diamond.lean` with the other abstract rewriting properties.
The separators inside the proof mark the three stages:

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
fixed point; only the `(≤)` direction of that equation holds, and it is
the only direction used. The counterexample is recorded with the
unfolding lemma in `Metatheory/Evaluation.lean`.

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
