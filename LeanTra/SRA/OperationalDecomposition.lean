/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Modality

/-!
# Operational decomposition

Operational semantics distinguishes the syntactic forms that construct
data from those that consume it: terms are either **introduction forms**
(constructors) or **elimination forms** (destructors), and the latter
further distinguish **major** arguments, which must be evaluated, from
**minor** ones, which need not be. Evaluation proceeds by reducing the
major arguments of an elimination form until they become introduction
forms, at which point a constructor meets a destructor and a
computational step fires.

An operational decomposition equips a `SRA` with the structure needed to
express that distinction without committing to a term representation.
Where `SRA` only knows that a relation can be lifted one layer of term
structure, via `~·`, this class says what that layer is made of: a
constructor part and a destructor part, and nothing else. It is the
setting in which Gentzen's inversion and commutation principles can be
stated algebraically, and therefore the layer on which the metatheory
rests.

## The class

Two data and fourteen axioms.

`introduction a` relates two introduction forms with the same outermost
constructor whose arguments are pairwise `a`-related. `elimination a b`
relates two elimination forms with the same outermost destructor whose
major arguments are pairwise `a`-related and whose minor arguments are
pairwise `b`-related.

Both are morphisms of the ambient structure: each preserves arbitrary
joins, composition and converse — three axioms for `introduction`, and
three for `elimination`, taken slot by slot (6). Both are oplax on the
unit (2). They are orthogonal: a constructor and a destructor never meet,
so their composite is `⊥` (1). Together they exhaust the strict
compatible refinement, `~a = ιa ⊔ ε(a, a)`, which is
the axiom that makes the decomposition a decomposition rather than a
pair of unrelated operations (1). Substitution passes oplaxly through
both (2), and the closure modality passes through the major slot of an
elimination form (1) — which is what makes the major argument of a closed
term closed in turn, and so keeps evaluation inside the fragment of
programs.

Orthogonality is assumed in one order only; the mirror follows by
converse, and is derived below.

## Derived operations

The coreflexives of the two forms, `introduction Δ` and
`elimination Δ Δ`, single out the terms that *are* introductions and
eliminations, as opposed to the relations between them. `valueCoreflexive`
is the closed part of the first: a value is a closed introduction form.
`majorProjection a := ε(a, Δ)` names the common case in which
two elimination forms are related through their major arguments alone,
which is the shape every statement about evaluation order takes.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA

universe u

class OperationalDecomposition (α : Type u)
  [Monoid α]
  [CompleteLattice α]
  [IsQuantale α]
  [IsInvolutiveQuantale α]
  extends SRA α where

  /-- The constructor part of the decomposition: `introduction a` relates
  two introduction forms with the same outermost constructor whose
  arguments are pairwise `a`-related. -/
  introduction : α → α

  /-- The destructor part: `elimination a b` relates two elimination forms
  with the same outermost destructor whose major arguments are pairwise
  `a`-related and whose minor arguments are pairwise `b`-related. -/
  elimination : α → α → α

  /-- `introduction` preserves arbitrary joins. -/
  protected introduction_join_preservation (s : Set α) : introduction (sSup s) = sSup (introduction '' s)
  /-- `introduction` preserves composition. -/
  protected introduction_compositionality (a b : α) : introduction (a * b) = introduction a * introduction b
  /-- `introduction` preserves converse. -/
  protected introduction_converse_commutation (a : α) : introduction (aᵒ) = (introduction a)ᵒ

  /-- `elimination` preserves arbitrary joins in the major (left) slot. -/
  protected elimination_join_preservation_left (s : Set α) (b : α) : elimination (sSup s) b = sSup ((fun a => elimination a b) '' s)
  /-- `elimination` preserves arbitrary joins in the minor (right) slot. -/
  protected elimination_join_preservation_right (a : α) (s : Set α) : elimination a (sSup s) = sSup ((fun b => elimination a b) '' s)
  /-- `elimination` preserves composition, slot by slot. -/
  protected elimination_compositionality (a a' b b' : α) : elimination (a * a') (b * b') = elimination a b * elimination a' b'
  /-- `elimination` preserves converse, slot by slot. -/
  protected elimination_converse_commutation (a b : α) : elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ

  /-- `introduction` is oplax on the unit. -/
  protected introduction_unit_oplaxity : introduction 1 ≤ 1
  /-- `elimination` is oplax on the unit. -/
  protected elimination_unit_oplaxity : elimination 1 1 ≤ 1

  /-- `introduction` and `elimination` are orthogonal. -/
  protected introduction_elimination_orthogonality (a b c : α) : introduction a * elimination b c ≤ ⊥

  /-- The strict compatible refinement decomposes into its
  constructor part and its destructor part, and into nothing else. -/
  protected scr_decomposition (a : α) : SRA.scr a = introduction a ⊔ elimination a a

  /-- Substitution distributes, oplaxly, over `introduction`. -/
  protected subst_introduction_oplaxity (a b : α) : SRA.subst (introduction a) b ≤ introduction (SRA.subst a b)
  /-- Substitution distributes, oplaxly, over `elimination`, slot by slot. -/
  protected subst_elimination_oplaxity (a₁ a₂ b : α) : SRA.subst (elimination a₁ a₂) b ≤ elimination (SRA.subst a₁ b) (SRA.subst a₂ b)

  /-- The closure modality passes through the major slot of an elimination form. -/
  protected box_elimination_oplaxity (a b : α) : SRA.box (elimination a b) ≤ elimination (SRA.box a) b

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [OperationalDecomposition α]



/-! ### Notation

Scoped notation for the two operations. Open with
`open scoped OperationalDecomposition`. -/

@[inherit_doc] scoped prefix:max "ι" => OperationalDecomposition.introduction
@[inherit_doc] scoped notation:max "ε(" a ", " b ")" => OperationalDecomposition.elimination a b



/-! ### Coreflexives and projections

The four abbreviations the rest of the development uses in place of the
raw operations: the terms that *are* introductions and eliminations,
the values among the former, and the common case of relating two
elimination forms through their major arguments alone. -/

/-- The coreflexive of introduction forms, `ι Δ`. -/
abbrev introductionCoreflexive : α := ι Δ
/-- The coreflexive of elimination forms, `ε(Δ, Δ)`. -/
abbrev eliminationCoreflexive : α := ε( Δ, Δ )
/-- The coreflexive of values, `□ introductionCoreflexive`. -/
abbrev valueCoreflexive : α := □ introductionCoreflexive
/-- `majorProjection a := ε(a, Δ)`: two elimination forms related through
their major arguments alone. -/
abbrev majorProjection (a : α) : α := ε( a, Δ )



/-! ### Derived laws

Monotonicity of both operations, from join preservation instantiated at a
two-element set; and the mirror of the orthogonality axiom, which is
assumed in one order only and recovered in the other by converse. -/

/-- `introduction` is monotone. -/
theorem introduction_monotonicity ⦃a b : α⦄ (h : a ≤ b) : ι a ≤ ι b := by
  have hsup : a ⊔ b = b := sup_of_le_right h
  have hs := OperationalDecomposition.introduction_join_preservation (α := α) {a, b}
  rw [Set.image_pair, sSup_pair, sSup_pair, hsup] at hs
  exact le_sup_left.trans hs.ge
/-- `elimination` is monotone in each slot. -/
theorem elimination_monotonicity ⦃a a' b b' : α⦄ (ha : a ≤ a') (hb : b ≤ b') : ε(a, b) ≤ ε(a', b') := by
  -- Monotone in the left slot via left join preservation.
  have hleft : ε(a, b) ≤ ε(a', b) := by
    have hsup_a : a ⊔ a' = a' := sup_of_le_right ha
    have h := OperationalDecomposition.elimination_join_preservation_left (α := α) {a, a'} b
    rw [Set.image_pair, sSup_pair, sSup_pair, hsup_a] at h
    exact le_sup_left.trans h.ge
  -- Monotone in the right slot via right join preservation.
  have hright : ε(a', b) ≤ ε(a', b') := by
    have hsup_b : b ⊔ b' = b' := sup_of_le_right hb
    have h := OperationalDecomposition.elimination_join_preservation_right (α := α) a' {b, b'}
    rw [Set.image_pair, sSup_pair, sSup_pair, hsup_b] at h
    exact le_sup_left.trans h.ge
  exact hleft.trans hright
/-- Symmetric orthogonality: `elimination b c * introduction a ≤ ⊥`,
derived from `introduction_elimination_orthogonality` via converse. -/
theorem elimination_introduction_orthogonality (a b c : α) : ε(b, c) * ι a ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_monotonicity_iff,
      IsInvolutiveQuantale.converse_bot_strictness,
      IsInvolutiveQuantale.converse_compositionality,
      ← OperationalDecomposition.introduction_converse_commutation,
      ← OperationalDecomposition.elimination_converse_commutation]
  exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _

end OperationalDecomposition
