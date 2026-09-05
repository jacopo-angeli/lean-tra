/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Algebra.KleeneStar

/-!
# Evaluation

Confluence, determinism and semantic equivalence are all formulated as
inequalities on relations. Two of the three, determinism and semantic
equivalence, are properties of *evaluation*, not of reduction. The
algebra therefore needs a notion of evaluation of its own, expressed in
the same operations as everything else and not imported from outside.
Supplying it is what this file does.

A rule of computation says how a term may change. It does not say when
the changing stops, nor in what order the opportunities to change are
taken. Evaluation supplies both, by iterating a rule along the strategy
that the operational decomposition has already fixed.

The starting observation is that a rule cannot fire wherever it pleases.
A destructor must inspect one of its arguments, and that argument might
not be in the right shape to begin with: `app(app(λx.t, s), r)` is not a
redex, and becomes one only once the inner application has been
contracted. Evaluation is therefore not the rule iterated blindly, but
the rule applied after the inspected argument has itself been brought
into shape.

`majorDescentRecursor` performs one such preparation: a
construction is accepted as it stands, a destruction has its inspected
argument handed back for evaluation, and the rule then acts on the
outcome. Iterating it to exhaustion gives `majorDescent`, the
least fixed point of that step. The recursion runs through the structure
of the term, not through time: it descends the spine of inspected
arguments as far as necessary, and the rule fires once at each level it
passes.

Because the step ends with the rule, `majorDescent` obliges the
rule to fire. A term already in constructed shape has nothing left to
prepare and no redex to offer, so it is related to nothing.
`majorDescent` is not yet a semantics: it can begin a computation but
cannot finish one.

`oneStepEvaluation` repairs the omission by applying the recursor not to
the rule but to the rule enlarged with the canonical forms. Where
`majorDescent` obliged the rule to fire, the enlarged one permits it not to:
a term in constructed shape is now related to itself, so a run may come
to rest. One step of evaluation is thus either an answer or a single
contraction. Its fixed-point equation and induction principle carry a
hypothesis the recursor's did not: enlarging the rule adds nothing only
if the rule cannot act on a canonical form in the first place, and that
is what `GIP` guarantees.

`bigStepEvaluation` iterates a single step any number of times, then
requires what is reached to be canonical. The iteration is the
reflexive-transitive closure; the requirement is a composition with the
canonical forms on the right. It is the requirement that makes this
evaluation rather than reduction: a run counts only if it ends where a
run may end.

With the constructions in place, the file establishes the laws they
obey, all under `GIP`. Introduction forms are inert: composing `Δ̄`
with `a^E`, with `(a^E)∗` or with `a^⇓` on the right never leaves `Δ̄`,
and `Δ̄ ≤ a^⇓` — every introduction form evaluates to itself, in zero
steps. A firing of the rule is one step of evaluation, and prefixing a
firing to a big-step run gives a big-step run. Unfolding a run once
shows it either at rest or one firing under an evaluated major
argument, `a^⇓ ≤ Δ̄ ⊔ ⟨a^⇓⟩ * a * a^⇓`. Finally, the least-fixed-point
origins of `a^E` and of the star combine into an induction principle
for `a^⇓` and its converse mirror.

One caution about the unfolding: the reference states it as an
*equation*, `a^⇓ = μx. Δ̄ ∨ ⟨x⟩ * a * x` (Proposition 29), but for the
definitions above only the `(≤)` direction holds, and the `(≥)`
direction is refutable — one step of `a^E` fires the rule at most once
per level of the major spine, while the right-hand side may fire twice
at the same level (in the λ-calculus, `app(I(II), s)` with `I = λx.x`
admits no `a^E`-step at all, yet `⟨a^⇓⟩ * a * a^⇓` relates it to a
value). The `(≤)` direction proved here is all the metatheory needs.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale LeanTra.Algebra
open OperationalDecomposition

namespace LeanTra.Metatheory

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-! ### The subterm recursion

The bundled OrderHom whose least fixed point runs the rule under the
inspected subterms, together with the two laws that pin down that fixed
point. Nothing further is used about the recursor once its fixed-point
equation and induction principle are established. -/

/-- One preparation step: a construction is accepted as it stands, a
destruction has its inspected argument handed back, and the rule then
acts on the result. Bundled as an `OrderHom` so its least fixed point
can be taken via `OrderHom.lfp`. -/
def majorDescentRecursor (a : α) : α →o α where
  toFun x := ((introductionCoreflexive : α) ⊔ majorProjection x) * a
  monotone' _ _ h := by
    exact mul_le_mul' (sup_le_sup_left
      (elimination_monotonicity h le_rfl) _) le_rfl

/-- The recursion that descends into inspected subterms until a
construction is reached: the least fixed point of the preparation step. -/
def majorDescent (a : α) : α := (majorDescentRecursor a).lfp

/-- Fixed-point law:
`majorDescent a = (introductionCoreflexive ⊔ majorProjection (majorDescent a)) * a`. -/
theorem majorDescent_fixpoint (a : α) :
  majorDescent a = ((introductionCoreflexive : α) ⊔ majorProjection (majorDescent a)) * a := by
  change (majorDescentRecursor a).lfp
        = ((introductionCoreflexive : α) ⊔ majorProjection (majorDescentRecursor a).lfp) * a
  exact ((majorDescentRecursor a).map_lfp).symm

/-- Fixed-point induction: `majorDescent a` lies below every
pre-fixed point of the preparation step. -/
theorem majorDescent_induction {a x : α}
    (h : ((introductionCoreflexive : α) ⊔ majorProjection x) * a ≤ x) :
    majorDescent a ≤ x :=
  (majorDescentRecursor a).lfp_le h

/-! ### One-step evaluation

Enlarging the rule with the canonical forms turns the recursion into an
evaluation whose runs may terminate: a term in constructed shape is now
related to itself. The fixed-point equation and induction principle
match `majorDescent`'s, restricted to the summand `majorProjection x * a`,
and they hold only for rules that cannot already act on a canonical
form, which is what `GIP` supplies. -/

/-- One-step evaluation: the recursion applied to the rule enlarged with
the canonical forms, so that a run may come to rest at an answer. -/
def oneStepEvaluation (a : α) : α := majorDescent (a ⊔ introductionCoreflexive)

/-- Collapse of the four summands of the enlarged recursor: composing a
canonical form with the rule is empty by `GIP`, composing the inspected
slot with a canonical form is empty by intro/elim orthogonality, and
composing a canonical form with itself is again a canonical form. What
remains is `introductionCoreflexive ⊔ majorProjection x * a`. -/
private theorem majorDescentRecursor_sup_introductionCoreflexive {a : α}
  (hGIP : GIP a)
  (x : α) :
  ((introductionCoreflexive : α) ⊔ majorProjection x) * (a ⊔ introductionCoreflexive) = introductionCoreflexive ⊔ majorProjection x * a := by
  have introduction_mul_rule_le_bot : ∀ y : α, OperationalDecomposition.introduction y * a ≤ (⊥ : α) := fun y => by
    calc OperationalDecomposition.introduction y * a
        ≤ OperationalDecomposition.introduction y
            * (majorProjection (introductionCoreflexive : α) * a) := by
          exact mul_le_mul' le_rfl hGIP
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
  rw [Quantale.mul_sup_distrib, Quantale.sup_mul_distrib,
      Quantale.sup_mul_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact (introduction_mul_rule_le_bot _).trans bot_le
    · exact le_sup_right
    · exact introductionCoreflexive_mul_self.le.trans le_sup_left
    · exact (majorProjection_mul_introductionCoreflexive_le_bot _).trans bot_le
  · refine sup_le ?_ ?_
    · exact le_sup_of_le_right
        (le_sup_of_le_left introductionCoreflexive_mul_self.ge)
    · exact le_sup_of_le_left le_sup_right

/-- Fixed-point law for one-step evaluation:
`oneStepEvaluation a = introductionCoreflexive ⊔ majorProjection (oneStepEvaluation a) * a`,
under `GIP a`. -/
theorem oneStepEvaluation_fixpoint {a : α} (hGIP : GIP a) :
    oneStepEvaluation a = introductionCoreflexive ⊔ majorProjection (oneStepEvaluation a) * a := by
  change majorDescent (a ⊔ introductionCoreflexive)
      = introductionCoreflexive
          ⊔ majorProjection (majorDescent (a ⊔ introductionCoreflexive)) * a
  conv_lhs => rw [majorDescent_fixpoint (a ⊔ introductionCoreflexive)]
  rw [majorDescentRecursor_sup_introductionCoreflexive hGIP]

/-- Fixed-point induction for one-step evaluation: `oneStepEvaluation a`
lies below every pre-fixed point of `introductionCoreflexive ⊔
majorProjection · * a`, under `GIP a`. -/
theorem oneStepEvaluation_induction {a x : α}
    (hGIP : GIP a)
    (h : (introductionCoreflexive : α) ⊔ majorProjection x * a ≤ x) :
    oneStepEvaluation a ≤ x := by
  refine majorDescent_induction ?_
  rw [majorDescentRecursor_sup_introductionCoreflexive hGIP]
  exact h

/-! ### Big-step evaluation

The reflexive-transitive closure of one-step, followed by a compulsory
canonical form. The latter is what separates evaluation from reduction:
a run counts only if it ends where a run may end. -/

/-- Big-step evaluation: any number of one-step evaluations, then a
canonical form. -/
def bigStepEvaluation (a : α) : α := (oneStepEvaluation a)∗ * introductionCoreflexive

/-! ### Introduction forms are inert

Under `GIP` a rule fires only through an elimination form, so an
introduction form offers it nothing: one step of evaluation returns the
same introduction form, and iterating changes nothing. Together with the
two containments `Δ̄ ≤ a^E` and `a ≤ a^E`, these absorption laws are the
elementary facts the rest of the development runs on. -/

/-- `Δ̄ ≤ a^E`: a term in constructed shape is an answer, so one step of
evaluation may return it unchanged. Immediate from the fixed-point
equation. -/
theorem introductionCoreflexive_le_oneStepEvaluation {a : α} (hgip : GIP a) :
    (introductionCoreflexive : α) ≤ oneStepEvaluation a :=
  le_sup_left.trans (oneStepEvaluation_fixpoint hgip).ge

/-- `a ≤ a^E`: a single firing of the rule is one step of evaluation.
By inversion the inspected argument of a firing already holds a
constructor, so no descent is needed before the rule acts. -/
theorem rule_le_oneStepEvaluation {a : α} (hgip : GIP a) :
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
theorem introductionCoreflexive_mul_oneStepEvaluation_le
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
theorem introductionCoreflexive_mul_star_oneStepEvaluation_le
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

/-! ### Basic laws of big-step evaluation

Every introduction form, and a fortiori every value, evaluates to
itself; and prefixing a firing of the rule to a big-step run gives a
big-step run. -/

/-- `Δ̄ ≤ a^⇓`: an introduction form evaluates to itself, in zero
one-step evaluations. Holds for every rule; in particular any relation
containing `(a^⇓)ᵒ * a^⇓` contains the whole of `Δ̄`. -/
theorem introductionCoreflexive_le_bigStepEvaluation {a : α} :
    (introductionCoreflexive : α) ≤ bigStepEvaluation a :=
  calc (introductionCoreflexive : α)
      = 1 * introductionCoreflexive := (one_mul _).symm
    _ ≤ (oneStepEvaluation a)∗ * introductionCoreflexive :=
        mul_le_mul' (LeanTra.Algebra.star_reflexivity _) le_rfl

/-- `Δ_κ ≤ a^⇓`: a value evaluates to itself. -/
theorem valueCoreflexive_le_bigStepEvaluation {a : α} :
    (valueCoreflexive : α) ≤ bigStepEvaluation a :=
  (SRA.box_le _).trans introductionCoreflexive_le_bigStepEvaluation

/-- `a * a^⇓ ≤ a^⇓`: firing the rule and then evaluating is
evaluating. From `a ≤ a^E` and star absorption. -/
theorem rule_mul_bigStepEvaluation_le {a : α} (hgip : GIP a) :
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
equation. The reverse direction fails: one step of `a^E` fires the rule
at most once per level of the major spine, whereas the right-hand side
may fire twice at the same level. In the λ-calculus with `I = λx.x`,
the term `app(I(II), s)` admits no `a^E`-step at all — its major
argument `I(II)` needs two firings at the top level to become a lambda —
yet the right-hand side relates it to the value of `app(I, s)`. So
`a^⇓` sits strictly below the least fixed point of the right-hand side,
and only the direction proved here is available. -/

/-- One unfolding of a big-step run, with the one-step evaluation in the
major slot: `a^⇓ ≤ Δ̄ ⊔ ⟨a^E⟩ * a * a^⇓`. The slot inherits from the
fixed-point equation of `a^E`; `bigStepEvaluation_unfold` upgrades it
to `⟨a^⇓⟩`. -/
theorem bigStepEvaluation_unfold_le {a : α} (hgip : GIP a) :
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
theorem bigStepEvaluation_unfold {a : α} (hgip : GIP a) :
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
theorem bigStepEvaluation_induction {a b : α} (hgip : GIP a)
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
theorem bigStepEvaluation_induction_op {a b : α} (hgip : GIP a)
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

end LeanTra.Metatheory

#print axioms LeanTra.Metatheory.majorDescent_fixpoint
#print axioms LeanTra.Metatheory.majorDescent_induction
#print axioms LeanTra.Metatheory.oneStepEvaluation_fixpoint
#print axioms LeanTra.Metatheory.oneStepEvaluation_induction
#print axioms LeanTra.Metatheory.bigStepEvaluation_unfold
#print axioms LeanTra.Metatheory.bigStepEvaluation_induction
#print axioms LeanTra.Metatheory.bigStepEvaluation_induction_op
