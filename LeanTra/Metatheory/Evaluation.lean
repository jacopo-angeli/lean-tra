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

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

open scoped LeanTra.Algebra
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
  have elimination_mul_introduction_le_bot : ∀ b c d : α, OperationalDecomposition.elimination b c * OperationalDecomposition.introduction d ≤ ⊥ := fun b c d => by
    rw [← IsInvolutiveQuantale.converse_monotonicity_iff,
        IsInvolutiveQuantale.converse_bot_strictness,
        IsInvolutiveQuantale.converse_compositionality,
        ← OperationalDecomposition.introduction_converse_commutation,
        ← OperationalDecomposition.elimination_converse_commutation]
    exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
  have introductionCoreflexive_mul_self : (introductionCoreflexive : α) * introductionCoreflexive = introductionCoreflexive := by
    change OperationalDecomposition.introduction 1
         * OperationalDecomposition.introduction 1
       = OperationalDecomposition.introduction 1
    rw [← OperationalDecomposition.introduction_compositionality, one_mul]
  have majorProjection_mul_introductionCoreflexive_le_bot : ∀ b : α, majorProjection b * (introductionCoreflexive : α) ≤ ⊥ := fun b => by
    change OperationalDecomposition.elimination b 1
       * OperationalDecomposition.introduction 1 ≤ ⊥
    exact elimination_mul_introduction_le_bot _ _ _
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

end LeanTra.Metatheory

#print axioms LeanTra.Metatheory.majorDescent_fixpoint
#print axioms LeanTra.Metatheory.majorDescent_induction
#print axioms LeanTra.Metatheory.oneStepEvaluation_fixpoint
#print axioms LeanTra.Metatheory.oneStepEvaluation_induction
