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

A `SRA` extends the involutive unital quantale with four data — the variable
co-equivalence `Δη`, the strict compatible refinement `tilde ·` (a weakly unital
morphism), relation substitution `·[·]` (an oplax bimorphism), and the closure
modality `□` — subject to the axioms recalled below. The derived operation
`hat · := Δη ⊔ tilde ·` (compatible refinement) is a `def`, not a field.

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
* `□` a deflationary idempotent monotone modality, with two absorption laws
  `□a * □b = □(□a * b) = □(a * □b)`, the lax multiplicativity
  `□a * □b ≤ □(a * b)`, collapse on variables `□Δη = ⊥`, and closure under
  substitution `(□a)[b] ≤ □a`. No co-equivalence conditions on `□1` are
  assumed — the advisor's axiom set does not include them.

## Design note — `□` as a primitive

LICS'26 §3.2.1 defines `□a := a[⊥]` and lists among its laws both the
strict multiplicativity `□(ϕ;ψ) = □ϕ;□ψ` and the identity
`□Δ ; ϕ ; □Δ ⊆ □ϕ` (the `e * a * e` decomposition). Both hold in the
*unscoped* term model, where `□R = R ∩ (closed × closed)` — the two
sides of each law simply compare pairs of closed terms. Both **fail**
in the *context-indexed* model of Example 3(2) — the model formalised
in `Instances/FirstOrder` — where `·[⊥]` no longer means "restrict to
closed endpoints" but "goes through the empty context".

Concrete counterexample to `□a = e * a * e` in the context-indexed
model. Take a signature with a constant symbol `c` and define
`R Γ t s := Nonempty Γ ∧ t = c ∧ s = c`. `R` is renaming-closed (there
is no map from an inhabited context into `Empty`, so the closure
hypothesis is vacuous on the branch that changes `Γ` to `∅`; on the
other branches `t = s = c` transports), hence a bona-fide `SynRel`.
But `R(∅) = ∅`, so `□R = R ∩ (·[⊥]) = ⊥`, whereas `e = □1` contains
the pair `(c, c)` in every non-empty context, and `e * R * e` still
carries `(c, c)` — so `e * R * e ≠ ⊥ = □R`. The advisor-supplied
composition axiom `□a * □b = □(a * □b)` similarly fails in the
context-indexed model.

`□` is therefore taken as a *primitive* field with exactly the axioms
the advisor supplied: `box_le`, `box_box`, `box_mono`,
`box_mul_box_eq_box_mul_{left,right}`, `box_mul_box_le`,
`box_varDiag_eq_bot`, `box_subst_le`. Only the lax half
`□a * □b ≤ □(a * b)` of the composition law is assumed; the reverse
`□(a * b) ≤ □a * □b` is not, and does not hold in the context-indexed
model. No co-equivalence conditions on `□1` are assumed — earlier drafts
carried `(□1)ᵒ ≤ □1` and `□1 ≤ □1 * □1` mirroring `Δη`, but they were
only used by the derivation of `□a = e * a * e`, which the current
axioms do not support (see the counterexample above); with that
derivation removed, no downstream lemma needs them either. Co-reflexivity
`□1 ≤ 1` is still available for free from `box_le` at `a := 1`.

Several of the `□` fields have no consumer in `Derived.lean`:
`box_mul_box_eq_box_mul_left`, `box_mul_box_eq_box_mul_right`,
`box_mul_box_le`, `box_varDiag_eq_bot`, and `box_subst_le` are the
advisor's axiomatisation of `□` and are expected to be consumed in the
operational-semantics chapter, not here.

Laws Gavazzo lists but that are derivable — e.g. closedness `·[b] ⊣ b » ·` from
join-preservation, `Δᵒ = Δ` and join-preservation of `·ᵒ` from the base — are
NOT fields; they are (or will be) proved in `Derived.lean`.

## Source symbol ↔ Lean name

The code is deliberately name-based: paper symbols are used in the thesis text
only, not in the sources. Two of the source's diacritics — a widetilde over the
argument and an overline that is drawn as a rule and vanishes from text
extraction — proved unreliable to transcribe, so all SRA operations are
referred to by their identifiers.

| Source symbol | Lean name                                 |
|---------------|-------------------------------------------|
| `Δη`          | `SRA.varDiag`                             |
| tilde         | `SRA.scr`                                 |
| hat           | `SRA.cr`                                  |
| `a[b]`        | `SRA.subst a b`                           |
| `·ᴴ`          | `SRA.howe`                                |
| `·§`          | `SRA.opHowe`                              |
| `b » c`       | `SRA.substResid b c`                      |
| `□a`          | `SRA.box a` (primitive field)             |
| `♦a`          | `SRA.dia a` (right adjoint of `SRA.box`)  |

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
compatible refinement `tilde ·`, relation substitution `·[·]`, and the closure
modality `□`, together with their defining axioms.

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


  /-- The closure modality `□`: `□a` is the largest closed sub-relation of
  `a` (informally, the part of `a` that only relates closed terms). Taken
  as primitive because the source's definition `□a := a[⊥]` picks out
  "endpoints are closed terms" only in the unscoped term model; in the
  context-indexed model of Example 3(2) (the one formalised in
  `Instances/FirstOrder`) it means "goes through the empty context", which
  is strictly stronger — see the module docstring's design note for the
  counterexample. -/
  box : α → α
  /-- `□` is deflationary: `□a ≤ a`. -/
  protected box_le (a : α) : box a ≤ a
  /-- `□` is idempotent: `□(□a) = □a`. -/
  protected box_box (a : α) : box (box a) = box a
  /-- `□` is monotone. -/
  protected box_mono ⦃a b : α⦄ : a ≤ b → box a ≤ box b
  /-- Left absorption for `□`: a composite `□a * □b` factors through a
  *single* application of `□` on the left, with the left factor un-boxed
  underneath. Together with `box_mul_box_eq_box_mul_right` this pins down the
  interaction of `□` with `*`. -/
  protected box_mul_box_eq_box_mul_left (a b : α) : box a * box b = box (box a * b)
  /-- Right absorption for `□`: symmetrically, the composite factors through
  a single `□` with the right factor un-boxed underneath. -/
  protected box_mul_box_eq_box_mul_right (a b : α) : box a * box b = box (a * box b)
  /-- Lax multiplicativity of `□`: `□a * □b ≤ □(a * b)`. Only this direction
  is assumed; the reverse `□(a * b) ≤ □a * □b` does NOT hold abstractly
  (the term-model witness in `Instances/FirstOrder/SRA.lean` shows the
  equality *does* hold in the intended model, but it is a model fact, not
  an algebraic law). -/
  protected box_mul_box_le (a b : α) : box a * box b ≤ box (a * b)
  /-- `□` collapses the variable co-equivalence: `□Δη = ⊥`. Only closed
  sub-relations of the pure-variable relation are the empty one. -/
  protected box_varDiag_eq_bot : box (varDiag : α) = ⊥
  /-- `□a` is closed under substitution: `(□a)[b] ≤ □a`. Since substitution
  is left-strict at `Δη`, only the `≤` direction is assumed abstractly — the
  reverse would need a full-fledged closure principle for substitution that
  the base algebra does not supply. -/
  protected box_subst_le (a b : α) : subst (box a) b ≤ box a

namespace SRA

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable [SRA α]

/-- Compatible refinement `hat · := Δη ⊔ tilde ·`. Derived operation, not a field of
`SRA`: two terms are compatibly refined by `a` when they are either the same
variable or built from the same operator with `a`-related sub-terms. -/
def cr (a : α) : α := varDiag ⊔ scr a

end SRA
