/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.TRA.Modality

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

An operational decomposition equips a `TRA` with the structure needed to
express that distinction without committing to a term representation.
Where `TRA` only knows that a relation can be lifted one layer of term
structure, via `~·`, this class says what that layer is made of: a
constructor part and a destructor part, and nothing else. It is the
setting in which Gentzen's inversion and conservation principles can be
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
four for `elimination`, whose join-preservation is taken slot by slot (7). Both are oplax on the
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

open scoped IsInvolutiveQuantale Quantale TRA

universe u

class OperationalDecomposition (α : Type u)
  [Monoid α]
  [CompleteLattice α]
  [IsQuantale α]
  [IsInvolutiveQuantale α]
  extends TRA α where

  /-- The constructor part of the decomposition: `introduction a` relates
  two introduction forms with the same outermost constructor whose
  arguments are pairwise `a`-related. -/
  introduction : α → α

  /-- The destructor part: `elimination a b` relates two elimination forms
  with the same outermost destructor whose major arguments are pairwise
  `a`-related and whose minor arguments are pairwise `b`-related. -/
  elimination : α → α → α

  /-- `introduction` preserves arbitrary non-empty joins. The empty case
  is excluded because it would forbid nullary constructors: a zero-arity
  intro form `c` has no premises, so `introduction φ` relates `c` to `c`
  independently of `φ`, and `introduction ⊥` would then differ from `⊥`.
  The paper only asks for ω-cocontinuity (Def. 6, page 11); non-empty
  joins is the strongest form compatible with nullary intro forms. -/
  protected introduction_join_preservation (s : Set α) (hs : s.Nonempty) :
      introduction (sSup s) = sSup (introduction '' s)
  /-- `introduction` preserves composition. -/
  protected introduction_compositionality (a b : α) : introduction (a * b) = introduction a * introduction b
  /-- `introduction` preserves converse. -/
  protected introduction_converse_commutation (a : α) : introduction (aᵒ) = (introduction a)ᵒ

  /-- `elimination` preserves arbitrary non-empty joins in the major (left)
  slot. See `introduction_join_preservation` for why the empty case is
  excluded. -/
  protected elimination_join_preservation_left (s : Set α) (hs : s.Nonempty) (b : α) :
      elimination (sSup s) b = sSup ((fun a => elimination a b) '' s)
  /-- `elimination` preserves arbitrary non-empty joins in the minor (right)
  slot. See `introduction_join_preservation` for why the empty case is
  excluded. -/
  protected elimination_join_preservation_right (a : α) (s : Set α) (hs : s.Nonempty) :
      elimination a (sSup s) = sSup ((fun b => elimination a b) '' s)
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
  protected scr_decomposition (a : α) : TRA.scr a = introduction a ⊔ elimination a a

  /-- Substitution distributes, oplaxly, over `introduction`, under the
  guard `Δη ≤ b`. Same binder-side obstruction as
  `TRA.subst_scr_oplaxity`: substituting under an `introduction` form
  crosses a binder, and the pointwise `b`-obligation forces the
  freshly-bound variable to be `b`-related to itself, which the guard
  supplies. Without the guard the law is refuted in the second-order
  λ-calculus model. At first order the guard is vacuous. Every use in
  the abstract development instantiates `b` with a relation containing
  the identity. -/
  protected subst_introduction_oplaxity (a b : α) (hb : TRA.varDiag ≤ b) :
      TRA.subst (introduction a) b ≤ introduction (TRA.subst a b)
  /-- Substitution distributes, oplaxly, over `elimination`, slot by slot. -/
  protected subst_elimination_oplaxity (a₁ a₂ b : α) : TRA.subst (elimination a₁ a₂) b ≤ elimination (TRA.subst a₁ b) (TRA.subst a₂ b)

  /-- The closure modality passes through the major slot of an elimination form. -/
  protected box_elimination_oplaxity (a b : α) : TRA.box (elimination a b) ≤ elimination (TRA.box a) b

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
two-element set; the mirror of the orthogonality axiom, which is
assumed in one order only and recovered in the other by converse; and
the calculus of the two coreflexives and of the major projection —
idempotence and self-conversion of `ι Δ`, fusion, converse and
monotonicity of `⟨·⟩ = ε(·, Δ)`, the orthogonality `⟨a⟩ * ι Δ ≤ ⊥`,
and the collapse `⟨ι Δ⟩ ≤ Δ`. -/

/-- `introduction` is monotone. -/
theorem introduction_monotonicity ⦃a b : α⦄ (h : a ≤ b) : ι a ≤ ι b := by
  have hsup : a ⊔ b = b := sup_of_le_right h
  have hs := OperationalDecomposition.introduction_join_preservation (α := α) {a, b}
    ⟨a, Set.mem_insert _ _⟩
  rw [Set.image_pair, sSup_pair, sSup_pair, hsup] at hs
  exact le_sup_left.trans hs.ge
/-- `elimination` is monotone in each slot. -/
theorem elimination_monotonicity ⦃a a' b b' : α⦄ (ha : a ≤ a') (hb : b ≤ b') : ε(a, b) ≤ ε(a', b') := by
  -- Monotone in the left slot via left join preservation.
  have hleft : ε(a, b) ≤ ε(a', b) := by
    have hsup_a : a ⊔ a' = a' := sup_of_le_right ha
    have h := OperationalDecomposition.elimination_join_preservation_left (α := α) {a, a'}
      ⟨a, Set.mem_insert _ _⟩ b
    rw [Set.image_pair, sSup_pair, sSup_pair, hsup_a] at h
    exact le_sup_left.trans h.ge
  -- Monotone in the right slot via right join preservation.
  have hright : ε(a', b) ≤ ε(a', b') := by
    have hsup_b : b ⊔ b' = b' := sup_of_le_right hb
    have h := OperationalDecomposition.elimination_join_preservation_right (α := α) a' {b, b'}
      ⟨b, Set.mem_insert _ _⟩
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

/-- The introduction coreflexive is idempotent under composition. -/
theorem introductionCoreflexive_mul_self :
    (introductionCoreflexive : α) * introductionCoreflexive = introductionCoreflexive := by
  change ι (1 : α) * ι 1 = ι 1
  rw [← OperationalDecomposition.introduction_compositionality, one_mul]

/-- The introduction coreflexive is symmetric under converse. -/
@[simp] theorem introductionCoreflexive_converse :
    (introductionCoreflexive : α)ᵒ = introductionCoreflexive := by
  change (ι (1 : α))ᵒ = ι 1
  rw [← OperationalDecomposition.introduction_converse_commutation,
      IsInvolutiveQuantale.converse_one]

/-- `⟨·⟩` is monotone. -/
theorem majorProjection_monotonicity ⦃a b : α⦄ (h : a ≤ b) :
    majorProjection a ≤ majorProjection b :=
  elimination_monotonicity h le_rfl

/-- `⟨·⟩` fuses under composition: `⟨a⟩ * ⟨b⟩ = ⟨a * b⟩`. Instance of
`elimination_compositionality` with the minor slot at the unit. -/
theorem majorProjection_compositionality (a b : α) :
    majorProjection a * majorProjection b = majorProjection (a * b) := by
  change ε(a, (1 : α)) * ε(b, 1) = ε(a * b, 1)
  rw [← OperationalDecomposition.elimination_compositionality, one_mul]

/-- `⟨·⟩` commutes with converse: `⟨a⟩ᵒ = ⟨aᵒ⟩`. -/
@[simp] theorem majorProjection_converse (a : α) :
    (majorProjection a)ᵒ = majorProjection aᵒ := by
  change (ε(a, (1 : α)))ᵒ = ε(aᵒ, 1)
  rw [← OperationalDecomposition.elimination_converse_commutation,
      IsInvolutiveQuantale.converse_one]

/-- A major projection followed by the introduction coreflexive is empty:
`⟨a⟩ * ι Δ ≤ ⊥`. Instance of the mirrored orthogonality. -/
theorem majorProjection_mul_introductionCoreflexive_le_bot (a : α) :
    majorProjection a * (introductionCoreflexive : α) ≤ ⊥ :=
  elimination_introduction_orthogonality 1 a 1

/-- `⟨ι Δ⟩ ≤ Δ`: two elimination forms whose major slots hold one and
the same introduction form are one and the same term. Combines the unit
oplaxity of both operations. -/
theorem majorProjection_introductionCoreflexive_le_one :
    majorProjection (introductionCoreflexive : α) ≤ 1 :=
  calc majorProjection (introductionCoreflexive : α)
      ≤ majorProjection 1 :=
        majorProjection_monotonicity
          OperationalDecomposition.introduction_unit_oplaxity
    _ ≤ 1 := OperationalDecomposition.elimination_unit_oplaxity

end OperationalDecomposition
