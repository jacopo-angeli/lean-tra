/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Structure.InvolutiveQuantale

/-!
# Syntax Relation Algebras

A `SRA` is the algebraic structure underlying Gavazzo's Term Relation Algebras,
formalised here over the involutive-quantale base (`IsInvolutiveQuantale`)
rather than over allegories, the two being equivalent in the one-object case.

A `SRA` extends the involutive unital quantale with three data — the variable
co-equivalence `Δη`, the strict compatible refinement `tilde ·` (a weakly unital
morphism), and relation substitution `·[·]` (an oplax bimorphism) — subject to
the axioms recalled below. The derived operation `hat · := Δη ⊔ tilde ·` (compatible
refinement) is a `def`, not a field.

## Axioms (fields of the class)

* `Δη` is a co-equivalence: symmetric, co-transitive, co-reflexive.
* `tilde ·` weakly unital: monotone, exact on composition and converse, oplax on the
  unit (`tilde Δ ≤ Δ`).
* `Δη` and `tilde ·` orthogonal (`Δη ; tilde a ≤ ⊥`).
* `Δ` is the least fixed point of `hat ·` (fixed-point law + structural induction).
* `·[·]` oplax bimorphism, strict on converse, join-preserving in the first
  argument.
* `(·, Δη, ·[·])` a monoid — recorded as `Prop` fields, NOT as a second `Monoid`
  instance (which would clash with the composition monoid).
* `·[·]` distributes over `tilde ·` (`tilde a[b] ≤ tilde (a[b])`).

Laws Gavazzo lists but that are derivable — e.g. closedness `·[b] ⊣ b » ·` from
join-preservation, `Δᵒ = Δ` and join-preservation of `·ᵒ` from the base — are
NOT fields; they are (or will be) proved in `Derived.lean`.

## Source symbol ↔ Lean name

The code is deliberately name-based: paper symbols are used in the thesis text
only, not in the sources. Two of the source's diacritics — a widetilde over the
argument and an overline that is drawn as a rule and vanishes from text
extraction — proved unreliable to transcribe, so all SRA operations are
referred to by their identifiers.

| Source symbol | Lean name              |
|---------------|------------------------|
| `Δη`          | `SRA.varDiag`          |
| tilde         | `SRA.scr`              |
| hat           | `SRA.cr`               |
| `a[b]`        | `SRA.subst a b`        |
| `·ᴴ`          | `SRA.howe`             |
| `·§`          | `SRA.opHowe`           |
| `b » c`       | `SRA.substResid b c`   |
| `□a`          | `SRA.box a` (`:= SRA.subst a ⊥`) |
| `♦a`          | `SRA.dia a` (`:= SRA.substResid ⊥ a`) |

Only the base-level involutive-quantale notations (`·ᵒ` for converse, `⇨ₗ` /
`⇨ᵣ` for the composition residuals, `·∗` for the Kleene star) remain scoped;
they are unambiguous and belong to Mathlib-style prose.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. (Presented there over allegories; the involutive-quantale
  presentation used here is equivalent in the one-object case.)
-/
@[expose] public section

universe u

open scoped IsInvolutiveQuantale

/-- A `SRA` (Syntax Relation Algebra) over an involutive unital quantale `α`.
Extends the base (`Monoid` + `CompleteLattice` + `IsQuantale` +
`IsInvolutiveQuantale`) with the variable co-equivalence `Δη`, the strict
compatible refinement `tilde ·`, and relation substitution `·[·]`, together with
their defining axioms.

This is the involutive-quantale presentation of the term relation algebra of
the paper cited in the module `References` block, whose base is there given
over allegories; the two are equivalent in the one-object case. -/
class SRA (α : Type u)
    [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] where
  /-- The variable co-equivalence `Δη`: the relation that holds between two
  terms exactly when they are the same variable. -/
  varDiag : α
  /-- Strict compatible refinement `tilde ·`: relates two terms built from the same
  outermost operator whose immediate sub-terms are pairwise related. -/
  scr : α → α
  /-- Relation substitution `·[·]`: `a[b]` relates two terms obtained from
  `a`-related terms by pointwise `b`-substitution on variables. -/
  subst : α → α → α
  /-- `Δη` is symmetric: swapping the endpoints of a variable-to-variable
  relation stays within the variable relation. -/
  protected varDiag_converse_le : varDiagᵒ ≤ varDiag
  /-- `Δη` is co-transitive: two variables related through an intermediate
  variable are related directly. -/
  protected varDiag_le_mul_self : varDiag ≤ varDiag * varDiag
  /-- `tilde ·` is monotone: refining the argument refines its strict compatible
  refinement. -/
  protected scr_mono ⦃a b : α⦄ : a ≤ b → scr a ≤ scr b
  /-- `tilde ·` preserves composition: relating two terms via a composite of
  sub-term relations is the same as composing their strict refinements. -/
  protected scr_mul (a b : α) : scr (a * b) = scr a * scr b
  /-- `tilde ·` preserves converse: turning the sub-term relation around commutes
  with taking the strict compatible refinement. -/
  protected scr_converse (a : α) : scr (aᵒ) = (scr a)ᵒ
  /-- Variables and compound terms are disjoint: a variable is never a term
  built from an outermost operator, so `Δη` and `tilde ·` cannot both hold. -/
  protected varDiag_mul_scr_le_bot (a : α) : varDiag * scr a ≤ ⊥
  /-- Substitution is monotone in the second argument: refining the
  substituent refines the result. Left-argument monotonicity follows from
  join-preservation in the first argument (`subst_sSup_left`). -/
  protected subst_mono_right ⦃a b b' : α⦄ : b ≤ b' → subst a b ≤ subst a b'
  /-- Substitution is oplax on composition in both arguments: substituting a
  composite is refined by composing the substitutions of its parts. -/
  protected subst_mul_le (a a' b b' : α) :
      subst (a * a') (b * b') ≤ subst a b * subst a' b'
  /-- Substitution commutes with converse: swapping the endpoints of a
  substitution is the substitution of the swapped relations. -/
  protected subst_converse (a b : α) : (subst a b)ᵒ = subst (aᵒ) (bᵒ)
  /-- Substitution preserves arbitrary joins in the first argument:
  substituting into a join of relations is the join of the substituted
  relations. -/
  protected subst_sSup_left (s : Set α) (b : α) :
      subst (sSup s) b = sSup ((fun a => subst a b) '' s)
  /-- `Δη` is a left unit for substitution: substituting into the variable
  relation is the identity. -/
  protected subst_varDiag_left (a : α) : subst varDiag a = a
  /-- `Δη` is a right unit for substitution: substituting variables for
  variables changes nothing. -/
  protected subst_varDiag_right (a : α) : subst a varDiag = a
  /-- Substitution is associative: substituting into a substitution is the
  same as substituting once with the composed substitution. -/
  protected subst_assoc (a b c : α) : subst (subst a b) c = subst a (subst b c)
  /-- Substitution is compatible with term structure: substituting into a
  strict compatible refinement refines the strict refinement of the
  substitution. -/
  protected subst_scr_le (a b : α) : subst (scr a) b ≤ scr (subst a b)
  /-- Fixed-point law for `hat ·`: the identity is a fixed point of compatible
  refinement, i.e. any term equals itself either as a variable or by having
  pairwise equal sub-terms. Inlined as `Δη ⊔ tilde 1 = 1` since `hat ·` is defined
  after the class. -/
  protected varDiag_sup_scr_one_eq : varDiag ⊔ scr 1 = 1
  /-- Structural induction: the identity is the *least* fixed point of `hat ·`,
  so any relation stable under compatible refinement contains the identity.
  Inlined as `Δη ⊔ tilde a ≤ a → 1 ≤ a` since `hat ·` is defined after the class. -/
  protected one_le_of_scr_sup_le ⦃a : α⦄ : varDiag ⊔ scr a ≤ a → 1 ≤ a

namespace SRA

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable [SRA α]

/-- Compatible refinement `hat · := Δη ⊔ tilde ·`. Derived operation, not a field of
`SRA`: two terms are compatibly refined by `a` when they are either the same
variable or built from the same operator with `a`-related sub-terms. -/
def cr (a : α) : α := varDiag ⊔ scr a

end SRA
