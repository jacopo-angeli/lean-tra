/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
public import LeanTra.SRA.Modality

/-!

# Operational decomposition

Operational semantics distinguishes between the syntactic forms that
construct data and those that consume it. In particular, terms can be
viewed as either **introduction forms** (constructors) or **elimination
forms** (destructors), with the latter further distinguishing between
major (eager) and minor (lazy) arguments. Evaluation proceeds by
evaluating the major arguments of an elimination form until they become
introduction forms, at which point Gentzen's Inversion Principle triggers
a computational step.

An operational decomposition equips a SRA with the algebraic structure
needed to express this distinction without referring directly to a
particular term representation. Its operations characterize relations
between introduction forms and elimination forms, with the latter
recording which arguments are major and which are minor.

This structure is needed to algebraize the basic notions of operational
semantics: introduction and elimination forms, values, closed major
arguments, and the interaction between constructors and destructors.
In particular, it provides the setting in which Gentzen's Inversion
Principle can be stated and used algebraically.

Given a SRA, an operational decomposition consists of weakly unital
orthogonal morphisms `introduction:α → α` and `elimination: α → α → α`
satisfying:

1. `scr a = introduction a ∨ elimination a a`
2. `subst · b` distributes over `introduction` and `elimination`
3. `box` distributes over `elimination · b`

These axioms ensure that the decomposition is compatible with the
existing SRA structure and that constructors and destructors are
orthogonal.



## Reference

Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.* LICS 2026

-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

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
  protected introduction_morphism_join (s : Set α) :  introduction (sSup s) = sSup (introduction '' s)
  /-- `introduction` preserves composition. -/
  protected introduction_morphism_composition (a b : α) : introduction (a * b) = introduction a * introduction b
  /-- `introduction` preserves converse. -/
  protected introduction_morphism_converse (a : α) : introduction (aᵒ) = (introduction a)ᵒ


  /-- `elimination` preserves arbitrary joins, taken componentwise on pairs. -/
  protected elimination_morphism_join (s : Set (α × α)) : elimination (sSup (Prod.fst '' s)) (sSup (Prod.snd '' s)) = sSup ((fun p : α × α => elimination p.1 p.2) '' s)
  /-- `elimination` preserves composition, slot by slot. -/
  protected elimination_morphism_composition(a a' b b' : α) : elimination (a * a') (b * b') = elimination a b * elimination a' b'
  /-- `elimination` preserves converse, slot by slot. -/
  protected elimination_morphism_converse (a b : α) : elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ


  /-- `elimination` is weakly unital. -/
  protected elimination_weakly_unital : elimination 1 1 ≤ 1
  /-- `introduction` is weakly unital. -/
  protected introduction_weakly_unital : introduction 1 ≤ 1


  /-- `introduction` and `elimination` are orthogonal. -/
  protected introduction_elimination_orthogonality (a b c : α) : introduction a * elimination b c ≤ ⊥


  /-- The strict compatible refinement decomposes into its
  constructor part and its destructor part, and into nothing else. -/
  protected cocartesian_decomposition (a : α) : SRA.scr a = introduction a ⊔ elimination a a


  /-- Substitution distributes, oplaxly, over `introduction`. -/
  protected substitution_distribution_introduction (a b : α) : SRA.subst (introduction a) b ≤ introduction (SRA.subst a b)
  /-- Substitution distributes, oplaxly, over `elimination`, slot by slot. -/
  protected substitution_distribution_elimination (a₁ a₂ b : α) : SRA.subst (elimination a₁ a₂) b ≤ elimination (SRA.subst a₁ b) (SRA.subst a₂ b)


  /-- The closure modality passes through the major slot of
  an elimination form. This is what makes the major argument of a closed
  term closed in turn, and therefore what keeps evaluation inside the
  fragment of programs. -/
  protected box_distribution_elimination (a b : α) : SRA.box (elimination a b) ≤ elimination (SRA.box a) b

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [OperationalDecomposition α]


/-- The coreflexives of introduction forms as `introduction Δ`. -/
abbrev introductionCoreflexive : α := introduction 1
/-- The coreflexives of elimination forms as `elimination Δ Δ`. -/
abbrev eliminationCoreflexive : α := OperationalDecomposition.elimination 1 1
/-- The coreflexive of values as `□ introductionCoreflexive`. -/
def valueCoreflexive : α := SRA.box (introductionCoreflexive : α)


/-- Since we will extensively relate elimination forms through their major arguments,
we introduce the abbreviating `majorProjection a ≜ elimination a Δ`. -/
abbrev majorProjection (a : α) : α := OperationalDecomposition.elimination a 1


/-- Monotonicity of `introduction`, from join preservation on a two-element subset. -/
theorem introduction_monotonicity ⦃a b : α⦄ (h : a ≤ b) :
    introduction a ≤ introduction b := by
  have hsup : a ⊔ b = b := sup_of_le_right h
  have hs := OperationalDecomposition.introduction_morphism_join (α := α) {a, b}
  rw [Set.image_pair, sSup_pair, sSup_pair, hsup] at hs
  exact le_sup_left.trans hs.ge

/-- Monotonicity of `elimination` in each slot, from componentwise join preservation on the two-element pair set `{(a, b), (a', b')}`. -/
theorem elimination_monotonicity ⦃a a' b b' : α⦄ (ha : a ≤ a') (hb : b ≤ b') :
    OperationalDecomposition.elimination a b ≤ OperationalDecomposition.elimination a' b' := by
  have hsup_a : a ⊔ a' = a' := sup_of_le_right ha
  have hsup_b : b ⊔ b' = b' := sup_of_le_right hb
  have h := OperationalDecomposition.elimination_morphism_join (α := α) {(a, b), (a', b')}
  rw [show (Prod.fst '' ({(a, b), (a', b')} : Set (α × α))) = {a, a'} from by
        simp [Set.image_pair],
      show (Prod.snd '' ({(a, b), (a', b')} : Set (α × α))) = {b, b'} from by
        simp [Set.image_pair],
      show ((fun p : α × α => OperationalDecomposition.elimination p.1 p.2)
              '' ({(a, b), (a', b')} : Set (α × α)))
            = {OperationalDecomposition.elimination a b,
                OperationalDecomposition.elimination a' b'} from by
        simp [Set.image_pair],
      sSup_pair, sSup_pair, sSup_pair, hsup_a, hsup_b] at h
  exact le_sup_left.trans h.ge

end OperationalDecomposition
