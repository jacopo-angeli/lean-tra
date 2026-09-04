/-
Master's thesis: Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
public import LeanTra.SRA.OperationalDecomposition

/-!
# Consistency of the `SRA` and `OperationalDecomposition` axioms

The class `SRA` bundles sixteen axioms and `OperationalDecomposition` extends
it with thirteen more. Any such axiomatic theory carries the risk of being
*inconsistent*: a hidden interaction between the axioms could force `⊥ = ⊤`
on every carrier, after which every theorem stated over the class would hold
vacuously and the entire development would be worthless. This file rules that
possibility out mechanically, by exhibiting a concrete algebra on which every
one of the twenty-nine axioms is directly discharged. A first-order theory
that has a model cannot derive a contradiction, so producing such an
inhabitant is a proof of consistency in the strict logical sense. The rest
of the file follows the natural order of that construction: fix the carrier,
install the involutive-quantale structure, discharge the SRA axioms,
discharge the operational-decomposition axioms, exhibit the non-degeneracy
witnesses, print the axiom trace.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Structure.Model

/-! ## The carrier

The key thing to internalise about the model is that the carrier of an SRA
is **not** itself a set of relations, it is the underlying set of an
abstract algebra whose elements happen to *behave* like relations. The
framework is pointfree: it does not care what its elements are, only that
they satisfy the axioms. Here we take the carrier to be `Toy := Prop`, the
type of Lean propositions. Propositional extensionality (`propext`)
identifies logically equivalent propositions, so up to that equality `Prop`
has exactly two elements: `True` (which we call `⊤`) and `False` (which we
call `⊥`), and the whole model lives on this two-element algebra. The
definition uses `def` rather than `abbrev` so that instance resolution does
not unfold `Toy` to `Prop` and the instances declared below stay attached
to `Toy` alone, without polluting `Prop`'s instance database. `def` is
still unfolded by definitional equality, which suffices for the
propext-based proofs. -/

/-- Two-element carrier: propositions themselves, viewed as a quantale under
conjunction. -/
def Toy : Type := Prop

namespace Toy

/-! ## The involutive-quantale layer

On top of `Toy` we install the operations that turn it into an involutive
unital quantale in the obvious way. Multiplication is conjunction, the unit
is `True`, the order is entailment, joins and meets come from `∨` and `∧`,
and the involution is the identity (since `∧` is commutative, contravariance
has nothing to do). Concretely `instMul`, `instOne`, `instMonoid` install
the monoidal part, `instCompleteLattice` inherits the complete Boolean
algebra of `Prop`, `instIsQuantale` checks that composition distributes
over arbitrary joins on both sides, and `instIsInvolutiveQuantale`
installs the identity converse. All proofs go by `propext` on the two-line
`⟨⟨...⟩, ...⟩` reshufflings that turn one propositional formula into
another. This is the standard Boolean-algebra reading of `Prop`,
specialised to the two-element case `{⊥, ⊤}`. -/

instance instMul : Mul Toy := ⟨And⟩
instance instOne : One Toy := ⟨True⟩

instance instMonoid : Monoid Toy where
  one_mul _ := propext ⟨And.right, fun h => ⟨trivial, h⟩⟩
  mul_one _ := propext ⟨And.left, fun h => ⟨h, trivial⟩⟩
  mul_assoc _ _ _ :=
    propext ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

instance instCompleteLattice : CompleteLattice Toy :=
  inferInstanceAs (CompleteLattice Prop)

instance instIsQuantale : IsQuantale Toy where
  mul_sSup_distrib a s := by
    change ((a ∧ sSup s : Prop)) = ⨆ b ∈ s, ((a : Prop) ∧ b)
    apply propext
    simp only [iSup_Prop_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨ha, p, hps, hp⟩; exact ⟨p, hps, ha, hp⟩
    · rintro ⟨p, hps, ha, hp⟩; exact ⟨ha, p, hps, hp⟩
  sSup_mul_distrib s a := by
    change ((sSup s ∧ (a : Prop) : Prop)) = ⨆ b ∈ s, (b ∧ (a : Prop))
    apply propext
    simp only [iSup_Prop_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨p, hps, hp⟩, ha⟩; exact ⟨p, hps, hp, ha⟩
    · rintro ⟨p, hps, hp, ha⟩; exact ⟨⟨p, hps, hp⟩, ha⟩

instance instIsInvolutiveQuantale : IsInvolutiveQuantale Toy where
  converse a := a
  converse_involutivity _ := rfl
  converse_compositionality _ _ := propext ⟨fun ⟨p, q⟩ => ⟨q, p⟩, fun ⟨p, q⟩ => ⟨q, p⟩⟩
  converse_monotonicity h := h

/-! ## The `SRA` instance

The four SRA operations on `Toy` are `varDiag := ⊤`, `scr _ := ⊥`
(constantly `⊥`, regardless of the argument), `subst a b := a ∧ b`, and
`j := ⊥`. These choices are not arbitrary: they are essentially forced by
the axioms themselves once the carrier has been fixed to two elements
(`subst varDiag b = b` combined with join preservation of `subst` forces
`varDiag = ⊤`, then `varDiag * scr a ≤ ⊥` forces `scr = const ⊥`, and so
on).

The model is not just formal manipulation, it has a genuine syntactic
reading. Consider the trivial term algebra with a single variable `x` and
no compound constructors, no application, no lambda, no first-order symbols
at all. Binary relations between terms of this algebra are subsets of
`{(x, x)}`, of which there are exactly two: the empty relation and the
singleton. The two-element carrier `{⊥, ⊤}` **is** the set of these two
relations, and under this reading `varDiag = {(x,x)} = ⊤` because `x` is a
variable equal to itself, `scr φ = ∅ = ⊥` because there are no compound
terms whose sub-parts could be `φ`-related, `subst φ ψ` collapses to
`φ ∧ ψ` because on a syntax with only one term substitution is trivial,
and `j = ∅ = ⊥` because `x` is not closed. So `Toy` is the pointfree
picture of the term-model on the empty signature with one variable, and
the axioms of `SRA` hold on it for the same reasons they hold on any term
model, just heavily degenerate. Concretely this means every axiom reduces
to a trivial statement about the two elements `⊥` and `⊤`: the `varDiag`
laws become `⊤ ≤ ⊤` and `⊤ ≤ ⊤ ∧ ⊤`, the unit laws for substitution become
`⊤ ∧ ψ = ψ` and `φ ∧ ⊤ = φ`, associativity of `subst` becomes
associativity of `∧`, and every axiom involving `scr` or `j` collapses
because those operations are constantly `⊥`. -/

instance instSRA : SRA Toy where
  varDiag := True
  scr _ := False
  subst a b := a ∧ b
  varDiag_symmetry := le_refl _
  varDiag_cotransitivity := fun h => ⟨h, h⟩
  scr_monotonicity _ _ _ := le_refl _
  scr_compositionality _ _ := propext ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  scr_converse_commutation _ := rfl
  varDiag_scr_orthogonality _ := fun ⟨_, h⟩ => h
  subst_monotonicity_right _ _ _ hb := fun ⟨ha, hb'⟩ => ⟨ha, hb hb'⟩
  subst_compositionality_oplax _ _ _ _ := fun ⟨⟨ha, ha'⟩, hb, hb'⟩ => ⟨⟨ha, hb⟩, ha', hb'⟩
  subst_converse_commutation _ _ := rfl
  subst_join_preservation_left s b := by
    change ((sSup s ∧ (b : Prop) : Prop)) = sSup ((fun a : Toy => (a ∧ b : Prop)) '' s)
    rw [sSup_image]
    apply propext
    simp only [iSup_Prop_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨p, hps, hp⟩, hb'⟩; exact ⟨p, hps, hp, hb'⟩
    · rintro ⟨p, hps, hp, hb'⟩; exact ⟨⟨p, hps, hp⟩, hb'⟩
  subst_varDiag_unit_left _ := propext ⟨And.right, fun h => ⟨trivial, h⟩⟩
  subst_varDiag_unit_right _ := propext ⟨And.left, fun h => ⟨h, trivial⟩⟩
  subst_associativity _ _ _ :=
    propext ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  subst_scr_oplaxity _ _ := fun ⟨h, _⟩ => h
  cr_fixpoint :=
    propext ⟨fun _ => trivial, fun _ => Or.inl trivial⟩
  cr_induction _ h := fun _ => h (Or.inl trivial)
  j := False
  j_coreflexivity _ := trivial
  j_symmetry h := h
  j_cotransitivity h := h.elim
  j_varDiag_orthogonality := fun ⟨h, _⟩ => h.elim

/-! ## The `OperationalDecomposition` instance

The same two-element carrier that discharges the `SRA` axioms extends to the
operational-decomposition layer with `introduction := fun _ => ⊥` and
`elimination := fun _ _ => ⊥`. Every axiom of the class collapses accordingly:
the decomposition `scr a = introduction a ⊔ elimination a a` becomes
`⊥ = ⊥ ⊔ ⊥`, orthogonality of introductions and eliminations becomes
`⊥ * ⊥ ≤ ⊥`, and the various monotonicity, compositionality and converse
laws all reduce to trivial statements about `⊥`. The instance is included in
this file because consistency of `OperationalDecomposition` on its own is not
enough: what matters is that its axioms do not contradict the underlying
`SRA` layer, and that requires exhibiting the two structures on the *same*
carrier. On `Toy` they coexist, so no such contradiction can exist. As with
the `SRA` instance, the derived operations (`introductionCoreflexive`,
`eliminationCoreflexive`, `valueCoreflexive`, the evaluation recursors) all
collapse to `⊥`, so no operational content is exercised; that job is left to
the concrete term models in `Instances/FirstOrder/` and
`Instances/SecondOrder/`. -/
instance instOperationalDecomposition : OperationalDecomposition Toy where
  introduction _ := False
  elimination _ _ := False
  introduction_join_preservation s := by
    refine le_antisymm False.elim ?_
    refine sSup_le ?_
    rintro _ ⟨_, _, rfl⟩
    exact le_refl _
  introduction_compositionality _ _ := propext ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  introduction_converse_commutation _ := rfl
  introduction_unit_oplaxity := fun h => h.elim
  elimination_join_preservation_left s b := by
    refine le_antisymm False.elim ?_
    refine sSup_le ?_
    rintro _ ⟨_, _, rfl⟩
    exact le_refl _
  elimination_join_preservation_right a s := by
    refine le_antisymm False.elim ?_
    refine sSup_le ?_
    rintro _ ⟨_, _, rfl⟩
    exact le_refl _
  elimination_compositionality _ _ _ _ := propext ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  elimination_converse_commutation _ _ := rfl
  elimination_unit_oplaxity := fun h => h.elim
  introduction_elimination_orthogonality _ _ _ := fun ⟨h, _⟩ => h
  scr_decomposition _ :=
    propext ⟨fun h => Or.inl h, fun h => h.elim (fun h => h) (fun h => h)⟩
  subst_introduction_oplaxity _ _ := fun ⟨h, _⟩ => h
  subst_elimination_oplaxity _ _ _ := fun ⟨h, _⟩ => h
  box_elimination_oplaxity _ _ := fun h => h.1.1

/-! ## Non-degeneracy

The last piece the consistency argument needs is a witness that the carrier
`Toy` is *not* itself already degenerate. If `Toy` collapsed to a single
element, the whole model would live inside a trivial algebra where every
statement holds vacuously, and its existence would say nothing about the
axioms. The two declarations below rule this out: `bot_ne_top` exhibits
`⊥ ≠ ⊤` in `Toy`, and `Nontrivial Toy` packages the same fact as the
Mathlib-standard typeclass. Together with the `#print axioms` commands at
the very bottom, they close the consistency argument mechanically: a model
exists, its carrier has more than one element, and no non-standard axiom is
required to state either fact. -/

instance instNontrivial : Nontrivial Toy where
  exists_pair_ne :=
    ⟨True, False, fun h => (h.mp trivial : False)⟩

theorem bot_ne_top : (⊥ : Toy) ≠ (⊤ : Toy) := fun h =>
  (h.symm.mp trivial : False)

end Toy

end LeanTra.Structure.Model

/-! ## Axiom trace

The two `#print axioms` commands below make the axiom footprint of the two
class instances visible in the build log. Both consist of `propext` and
`Quot.sound` only, without `Classical.choice`, so consistency of `SRA` and
`OperationalDecomposition` is established already in the choice-free
fragment of Lean. What this file does *not* certify is that the axioms
have any non-trivial content: on a two-element carrier the compatible
refinement and the whole operational-decomposition layer are forced to
collapse, so no substantive propagation through term structure is being
tested. That job is delegated to the term-model instances in
`Instances/FirstOrder.lean` and `Instances/SecondOrder.lean`, where
`scr` really does propagate a relation through the constructors of a
genuine signature and `j` really does isolate closed terms. This file has
the complementary role: not to check that the axioms *say something*, but
to check that what they say is *not internally contradictory*. -/

#print axioms LeanTra.Structure.Model.Toy.instSRA
#print axioms LeanTra.Structure.Model.Toy.instOperationalDecomposition
