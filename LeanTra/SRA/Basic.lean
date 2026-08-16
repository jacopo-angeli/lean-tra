/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.InvolutiveQuantale

/-!
# Syntax Relation Algebras

An algebra of relations over an unspecified syntax. The base involutive
quantale is extended with the three operations that make its elements behave
like relations *between terms*: a distinguished relation of variables, a way
to lift a relation one layer of term structure, and a substitution operation.

## Relation to Definition 6 of the reference

There a Term Relation Algebra is a locally-complete allegory carrying the same
operations. The class below has a single carrier, so that allegory is
one-object, and a one-object locally-complete allegory is an involutive
quantale satisfying the modular law. That law is the one axiom of the
reference's base not assumed below; a structure that needs it can require it
separately.

The remaining differences have a common shape: what Definition 6 assumes,
completeness of the lattice supplies.

* It asks the compatible refinement to be ω-cocontinuous. Monotonicity is
  enough, the fixed points coming from Knaster–Tarski rather than from
  colimits of ω-chains.
* It postulates a uniform unique solution of `x = cr x * a`. `SRA.howe` is
  that least fixed point, and its uniqueness is a theorem
  (`SRA.howe_unique`).
* It asks `(·, Δη, ·[·])` to be a *closed* monoid. The monoid laws are axioms
  below; closedness is not, since `SRA.substResid` is the join of its own
  candidates and the adjunction follows from join-preservation of substitution
  in its first argument.

The class below therefore assumes strictly less than Definition 6. The closure
constant `j`, and the modality derived from it, have no counterpart there.

## The class

Four data and twenty axioms.

The variable relation `Δη` is a co-equivalence: symmetric and co-transitive
(2 axioms). The strict compatible refinement `tilde ·` is a weakly unital
morphism: monotone, exact on composition and on converse (3), and disjoint
from `Δη`, since a variable is never a compound term (1). Substitution `·[·]`
is an oplax bimorphism, strict on converse, join-preserving on the left, with
`Δη` as two-sided unit, associative, and oplax over `tilde ·` (8). Two further
axioms make `Δ` the least fixed point of the compatible refinement — the
fixed-point equation and structural induction — which is what lets proofs
about all terms run by induction on term structure (2). The closure constant
`j` is co-reflexive, symmetric, co-transitive, and orthogonal to `Δη` (4).

The unit and associativity of substitution are recorded as `Prop` fields
rather than a second `Monoid` instance, which would clash with the one
carrying composition.

## Derived operations

Two operations are `def`s below rather than fields, because their laws follow
from the axioms above:

* `cr a := Δη ⊔ tilde a`, the compatible refinement — the strict one, widened
  to hold on variables;
* `box a := j * a * j`, the closure modality — the pairs of `a` whose two
  endpoints are closed. Its laws are theorems in `SRA/Derived.lean`.

One law of `box` does not follow: `subst (box a) b ≤ box a`. No condition on
`j` alone yields it through the oplax `subst_compositionality_oplax`, and the first-order term
model of `Instances/FirstOrder`, where `j` is the identity on closed terms,
exhibits a relation and a substituent for which it fails. It is therefore
absent from the class rather than assumed.

## Naming

Identifiers are used throughout in place of the reference's symbols, which
appear in the thesis text only. The table below covers the whole `SRA` layer,
not just this file.

| Reference symbol | Lean name                              |
|------------------|----------------------------------------|
| `Δη`             | `SRA.varDiag`                          |
| tilde            | `SRA.scr`                              |
| hat              | `SRA.cr`                               |
| `a[b]`           | `SRA.subst a b`                        |
| `·ᴴ`             | `SRA.howe`                             |
| `·§`             | `SRA.opHowe`                           |
| `b » c`          | `SRA.substResid b c`                   |
| `j` (`□Δ`)       | `SRA.j`                                |
| `□a`             | `SRA.box a`                            |
| `♦a`             | `SRA.dia a`                            |

The notations in scope are those of the algebraic base: `·ᵒ` for converse and
`⇨ₗ`, `⇨ᵣ` for the composition residuals.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

universe u

open scoped IsInvolutiveQuantale

/-- A `SRA` (Syntax Relation Algebra) over an involutive unital quantale `α`.
Extends the base (`Monoid` + `CompleteLattice` + `IsQuantale` +
`IsInvolutiveQuantale`) with the variable co-equivalence `Δη`, the strict
compatible refinement `tilde ·`, relation substitution `·[·]`, and the closure
constant `j`, together with their defining axioms. The closure modality `□`
is derived as `j * · * j` (see `Structure/Derived.lean`).

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
  protected varDiag_symmetry : varDiagᵒ ≤ varDiag
  /-- `Δη` is co-transitive: two variables related through an intermediate
  variable are related directly. -/
  protected varDiag_cotransitivity : varDiag ≤ varDiag * varDiag
  /-- `tilde ·` is monotone: refining the argument refines its strict compatible
  refinement. -/
  protected scr_monotonicity ⦃a b : α⦄ : a ≤ b → scr a ≤ scr b
  /-- `tilde ·` preserves composition: relating two terms via a composite of
  sub-term relations is the same as composing their strict refinements. -/
  protected scr_compositionality (a b : α) : scr (a * b) = scr a * scr b
  /-- `tilde ·` preserves converse: turning the sub-term relation around commutes
  with taking the strict compatible refinement. -/
  protected scr_converse_commutation (a : α) : scr (aᵒ) = (scr a)ᵒ
  /-- Variables and compound terms are disjoint: a variable is never a term
  built from an outermost operator, so `Δη` and `tilde ·` cannot both hold. -/
  protected varDiag_scr_orthogonality (a : α) : varDiag * scr a ≤ ⊥
  /-- Substitution is monotone in the second argument: refining the
  substituent refines the result. Left-argument monotonicity follows from
  join-preservation in the first argument (`subst_join_preservation_left`). -/
  protected subst_monotonicity_right ⦃a b b' : α⦄ : b ≤ b' → subst a b ≤ subst a b'
  /-- Substitution is oplax on composition in both arguments: substituting a
  composite is refined by composing the substitutions of its parts. -/
  protected subst_compositionality_oplax (a a' b b' : α) :
      subst (a * a') (b * b') ≤ subst a b * subst a' b'
  /-- Substitution commutes with converse: swapping the endpoints of a
  substitution is the substitution of the swapped relations. -/
  protected subst_converse_commutation (a b : α) : (subst a b)ᵒ = subst (aᵒ) (bᵒ)
  /-- Substitution preserves arbitrary joins in the first argument:
  substituting into a join of relations is the join of the substituted
  relations. -/
  protected subst_join_preservation_left (s : Set α) (b : α) :
      subst (sSup s) b = sSup ((fun a => subst a b) '' s)
  /-- `Δη` is a left unit for substitution: substituting into the variable
  relation is the identity. -/
  protected subst_varDiag_unit_left (a : α) : subst varDiag a = a
  /-- `Δη` is a right unit for substitution: substituting variables for
  variables changes nothing. -/
  protected subst_varDiag_unit_right (a : α) : subst a varDiag = a
  /-- Substitution is associative: substituting into a substitution is the
  same as substituting once with the composed substitution. -/
  protected subst_associativity (a b c : α) : subst (subst a b) c = subst a (subst b c)
  /-- Substitution is compatible with term structure: substituting into a
  strict compatible refinement refines the strict refinement of the
  substitution. -/
  protected subst_scr_oplaxity (a b : α) : subst (scr a) b ≤ scr (subst a b)
  /-- Fixed-point law for `hat ·`: the identity is a fixed point of compatible
  refinement, i.e. any term equals itself either as a variable or by having
  pairwise equal sub-terms. Inlined as `Δη ⊔ tilde 1 = 1` since `hat ·` is defined
  after the class. -/
  protected cr_fixpoint : varDiag ⊔ scr 1 = 1
  /-- Structural induction: the identity is the *least* fixed point of `hat ·`,
  so any relation stable under compatible refinement contains the identity.
  Inlined as `Δη ⊔ tilde a ≤ a → 1 ≤ a` since `hat ·` is defined after the class. -/
  protected cr_induction ⦃a : α⦄ : varDiag ⊔ scr a ≤ a → 1 ≤ a


  /-- The closure constant `j`: informally the identity restricted to closed
  terms, from which `□a := j * a * j` reads off "the pairs of `a` whose two
  endpoints are closed". Given as a bare element rather than an operation,
  since the whole modal structure is generated by its three co-equivalence
  axioms below plus orthogonality to `Δη`. -/
  j : α
  /-- `j` is co-reflexive: `j ≤ 1`. Mirrors `varDiag_le_one` — but `varDiag`
  is not co-reflexive by axiom, only in the `Δη ⊔ tilde ·` decomposition; here
  `j ≤ 1` is a genuine axiom. -/
  protected j_coreflexivity : j ≤ 1
  /-- `j` is symmetric: `jᵒ ≤ j`. The full equality `jᵒ = j` is derived in
  `SRA/Derived.lean` by the same one-line involution argument as
  `varDiag_converse`. -/
  protected j_symmetry : jᵒ ≤ j
  /-- `j` is co-transitive: `j ≤ j * j`. Together with the co-reflexivity
  `j ≤ 1` it forces the reverse `j * j ≤ j` (since `j * j ≤ 1 * j = j`), so
  the equality `j * j = j` holds — see `SRA/Derived.lean`. -/
  protected j_cotransitivity : j ≤ j * j
  /-- `j` and `Δη` are orthogonal on the right: `j * Δη ≤ ⊥`. Mirrors the
  existing `varDiag_scr_orthogonality`. Its role is to discharge the derived
  `box_varDiag_eq_bot : box Δη = ⊥`, via `j * Δη * j ≤ ⊥ * j = ⊥`. -/
  protected j_varDiag_orthogonality : j * varDiag ≤ ⊥

namespace SRA

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable [SRA α]

/-- Compatible refinement `hat · := Δη ⊔ tilde ·`. Derived operation, not a field of
`SRA`: two terms are compatibly refined by `a` when they are either the same
variable or built from the same operator with `a`-related sub-terms. -/
def cr (a : α) : α := varDiag ⊔ scr a

/-- The closure modality `□ a := j * a * j`. Derived operation, not a field of
`SRA` in the current presentation (previously primitive; see the module
docstring's design note). Reads as "the pairs of `a` whose two endpoints are
closed", with `j` the closure constant. -/
def box (a : α) : α := SRA.j * a * SRA.j

scoped prefix:max "~" => SRA.scr
scoped prefix:max "⌃" => SRA.cr
scoped prefix:max "□" => SRA.box
scoped notation:max a "⟦" b "⟧" => SRA.subst a b

end SRA
