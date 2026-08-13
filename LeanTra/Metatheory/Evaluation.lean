/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Algebra.KleeneStar

/-!
# Evaluation

This development expresses the metatheory of a formal system in a
point-free algebra of relations: properties are stated as inequalities
between relations, built from composition, converse, join and
substitution, rather than as quantified statements about terms and
derivations. Confluence, determinism and semantic equivalence are all
formulated that way.

Two of those three are not properties of reduction. Determinism is a
property of the evaluation a rule induces, and semantic equivalence is
defined from evaluation as well. The algebra therefore needs a notion of
evaluation of its own, expressed in the same operations as everything
else and not imported from outside. Supplying it is what this file does.

A rule of computation says how a term may change. It does not say when
the changing stops, nor in what order the opportunities to change are
taken. Evaluation supplies both, by iterating a rule along the strategy
that the operational decomposition has already fixed.

The starting observation is that a rule cannot fire wherever it pleases.
A destructor must inspect one of its arguments, and that argument might
not be in the right shape to begin with: in `app(app(λx.t, s), r)` the
outer application is not a redex, and becomes one only once the inner
one has been contracted. Evaluation is therefore not the rule iterated
blindly, but the rule applied after the inspected argument has itself
been brought into shape.

`majorSubtermRecursionStep` performs one such preparation: a construction
is accepted as it stands, a destruction has its inspected argument handed
back for evaluation, and the rule then acts on the outcome. Iterating it
to exhaustion gives `majorSubtermRecursion`, the least relation closed
under that step. The recursion runs through the structure of the term, not
through time: it descends the spine of inspected arguments as far as
necessary, and the rule fires once at each level it passes.

Because the step ends with the rule, `majorSubtermRecursion` obliges the
rule to fire. A term already in constructed shape has nothing left to
prepare and no redex to offer, so it is related to nothing at all. This
is the sense in which the recursor is not yet a semantics: it can begin a
computation but it cannot finish one.

`majorSubtermRecursion_solution` is the equation the recursor satisfies, and
`majorSubtermRecursion_least` says it lies below every other solution.The
equation is not arbitrary. Howe's construction is the least solution of
`x = x̂ ; a`, where `x̂` refines compatibly everywhere: under constructors,
and in every argument of a destructor. The operational decomposition splits
that refinement into an introduction part and an elimination part, and the
recursor keeps the shape while restricting both. The introduction part becomes
the bare canonical forms, so that nothing is evaluated under a constructor;
the elimination part keeps the recursion in the inspected slot and drops it
elsewhere, so that minor arguments are left alone. What remains is the
evaluation order the decomposition declares, written as an equation.

`oneStepEvaluation` repairs the omission by applying the recursor not to
the rule but to the rule enlarged with the canonical forms. Where the
recursor obliged the rule to fire, the enlarged one permits it not to:
a term in constructed shape is now related to itself, so a run may come
to rest. One step of evaluation is thus either an answer or a single
contraction. `oneStepEvaluation_solution` and `oneStepEvaluation_least`
are the two laws for it. Both carry a hypothesis the recursor's did not:
enlarging the rule adds nothing only if the rule cannot act on a canonical
form in the first place, and that is what the Gentzen inversion
principle `GIP` guarantees.

`bigStepEvaluation` iterates a single step any number of times, then
requires what is reached to be canonical. The iteration is the
reflexive-transitive closure; the requirement is a composition with the
canonical forms on the right. It is the requirement that makes this
evaluation rather than reduction: a run counts only if it ends where a
run may end. In the call-by-value lambda calculus, with beta restricted
to value arguments, this is the usual big-step judgement. Being built by
iteration rather than as a fixed point, it carries no characterisation
of its own; the corresponding one is proved where it is used.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.* LICS 2026
-/
@[expose] public section

open scoped LeanTra.Confluence

open OperationalDecomposition

namespace LeanTra.Metatheory

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- To evaluate a destruction, the subterm it inspects must be evaluated
first; only then can the rule fire. This map performs one such step. It
is monotone, so it has a least fixed point. -/
def majorSubtermRecursionStep (a : α) : α →o α where
  toFun x := ((introductionCoreflexive : α) ⊔ majorProjection x) * a
  monotone' _ _ h := by
    exact mul_le_mul' (sup_le_sup_left
      (elimination_monotonicity h le_rfl) _) le_rfl

/-- That least fixed point: recursion that descends into inspected
subterms until a construction is reached. Taking the least one means two
terms are related only when a finite descent relates them. -/
def majorSubtermRecursion (a : α) : α := (majorSubtermRecursionStep a).lfp

/-- The recursor solves its equation: a construction, or a destruction
whose inspected subterm has already been evaluated, with the rule acting
on the result. A fixed point does not unfold by itself, so this is how a
single step is exposed. -/
theorem majorSubtermRecursion_solution (a : α) :
  majorSubtermRecursion a = ((introductionCoreflexive : α) ⊔ majorProjection (majorSubtermRecursion a)) * a := by
  change (majorSubtermRecursionStep a).lfp
        = ((introductionCoreflexive : α) ⊔ majorProjection (majorSubtermRecursionStep a).lfp) * a
  exact ((majorSubtermRecursionStep a).map_lfp).symm

/-- The recursor also lies below every other solution of that equation.
The two laws together are all that is known about it, and all that is
needed: the construction can be set aside from here on. -/
theorem majorSubtermRecursion_least {a x : α}
    (h : ((introductionCoreflexive : α) ⊔ majorProjection x) * a ≤ x) :
    majorSubtermRecursion a ≤ x :=
  (majorSubtermRecursionStep a).lfp_le h

/-- The recursor alone never brings a run to rest, since a term already
in constructed shape has nothing to descend into and no redex to offer.
Enlarging the rule with the canonical forms repairs this: such a term is
now related to itself, and a single step is either an answer or one
contraction. -/
def oneStepEvaluation (a : α) : α := majorSubtermRecursion (a ⊔ introductionCoreflexive)

/-- By construction one-step evaluation is the least solution of the
recursor's equation at the enlarged rule, `x = (‾Δ ∨ ⟨x⟩) ; (a ∨ ‾Δ)`,
which is not the equation one wants. Distributing gives four summands,
and three of them collapse. Composing a canonical form with the rule is
empty, since `GIP` keeps the rule from acting on one; composing the
inspected slot with a canonical form is empty by orthogonality of
introductions and eliminations; and a canonical form composed with
itself is again a canonical form. Only the descent survives untouched,
and what remains is `‾Δ ∨ ⟨x⟩ ; a`. -/
private theorem majorSubtermRecursionStep_sup_introductionCoreflexive {a : α}
  (hGIP : GIP a)
  (x : α) :
  ((introductionCoreflexive : α) ⊔ majorProjection x) * (a ⊔ introductionCoreflexive) = introductionCoreflexive ⊔ majorProjection x * a := by
  have elimination_mul_introduction_le_bot : ∀ b c d : α, OperationalDecomposition.elimination b c * OperationalDecomposition.introduction d ≤ ⊥ := fun b c d => by
    rw [← IsInvolutiveQuantale.converse_le_converse_iff,
        IsInvolutiveQuantale.converse_bot,
        IsInvolutiveQuantale.mul_converse,
        ← OperationalDecomposition.introduction_morphism_converse,
        ← OperationalDecomposition.elimination_morphism_converse]
    exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
  have introductionCoreflexive_mul_self : (introductionCoreflexive : α) * introductionCoreflexive = introductionCoreflexive := by
    change OperationalDecomposition.introduction 1
         * OperationalDecomposition.introduction 1
       = OperationalDecomposition.introduction 1
    rw [← OperationalDecomposition.introduction_morphism_composition, one_mul]
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

/-- One-step evaluation therefore solves `x = ‾Δ ∨ ⟨x⟩ ; a`: a term is
either already canonical, or its inspected subterm is evaluated and the
rule fires on the result. The hypothesis is what the collapse above
consumes, and it is why this law is conditional where the recursor's was
not. -/
theorem oneStepEvaluation_solution {a : α} (hGIP : GIP a) :
    oneStepEvaluation a = introductionCoreflexive ⊔ majorProjection (oneStepEvaluation a) * a := by
  change majorSubtermRecursion (a ⊔ introductionCoreflexive)
      = introductionCoreflexive
          ⊔ majorProjection (majorSubtermRecursion (a ⊔ introductionCoreflexive)) * a
  conv_lhs => rw [majorSubtermRecursion_solution (a ⊔ introductionCoreflexive)]
  rw [majorSubtermRecursionStep_sup_introductionCoreflexive hGIP]

/-- And it lies below every other solution of that equation. With both
laws established, one-step evaluation is determined without reference to
the fixed point it was built from. -/
theorem oneStepEvaluation_least {a x : α}
    (hGIP : GIP a)
    (h : (introductionCoreflexive : α) ⊔ majorProjection x * a ≤ x) :
    oneStepEvaluation a ≤ x := by
  refine majorSubtermRecursion_least ?_
  rw [majorSubtermRecursionStep_sup_introductionCoreflexive hGIP]
  exact h

/-- One step contracts once and halts. Evaluation contracts until
nothing remains, then reports what was reached: iterate one step, and
require the result to be canonical. That requirement is what separates
evaluation from reduction, which may stop anywhere. -/
def bigStepEvaluation (a : α) : α := (oneStepEvaluation a)∗ * introductionCoreflexive

end LeanTra.Metatheory

#print axioms LeanTra.Metatheory.majorSubtermRecursion_solution
#print axioms LeanTra.Metatheory.majorSubtermRecursion_least
#print axioms LeanTra.Metatheory.oneStepEvaluation_solution
#print axioms LeanTra.Metatheory.oneStepEvaluation_least
