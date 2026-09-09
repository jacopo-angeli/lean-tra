/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.InvolutiveQuantale

/-!
# Term Relation Algebras

An algebra of relations over an unspecified syntax. The base involutive
quantale is extended with the three operations that make its elements
behave like relations *between terms*: a distinguished relation of
variables, a way to lift a relation one layer of term structure, and a
substitution operation.

## Relation to Definition 6 of the reference

There a Term Relation Algebra is a locally-complete allegory carrying the
same operations. The class below has a single carrier, so that allegory
is one-object, and a one-object locally-complete allegory is an
involutive quantale satisfying the modular law. That law is the one axiom
of the reference's base not assumed below; a structure that needs it can
require it separately.

The remaining differences have a common shape: what Definition 6 assumes,
completeness of the lattice supplies.

* It asks the compatible refinement to be ω-cocontinuous. Monotonicity is
  enough, the fixed points coming from Knaster–Tarski rather than from
  colimits of ω-chains.
* It postulates a uniform unique solution of `x = ⌃x * a`. `TRA.howe` is
  that least fixed point, and its uniqueness is a theorem
  (`TRA.howe_unique`, in `TRA/Howe.lean`).
* It asks `(·, Δη, ·⟦·⟧)` to be a *closed* monoid. The monoid laws are
  axioms below; closedness is not, since `TRA.substResid` is the join of
  its own candidates and the adjunction follows from join-preservation of
  substitution in its first argument.

One assumption is weakened rather than dropped: the oplaxity of
substitution over compatible refinement carries the guard `Δη ≤ b`,
absent from Definition 6, because the unguarded form fails in the
well-scoped higher-order term model (see `subst_scr_oplaxity` below).

The class below therefore assumes strictly less than Definition 6. The
closure constant `j`, and the modality derived from it, have no
counterpart there.

## The class

Four data and twenty axioms.

The variable relation `Δη` is a co-equivalence: symmetric and
co-transitive (2). The strict compatible refinement `~·` is a morphism:
monotone, exact on composition and on converse (3), and disjoint from
`Δη`, since a variable is never a compound term (1). Substitution `·⟦·⟧`
is monotone in its second argument, an oplax bimorphism, strict on
converse, join-preserving on the left, has `Δη` as a two-sided unit, is
associative, and is oplax over `~·` (8). Two further axioms make `Δ` the
least fixed point of the compatible refinement — the fixed-point equation
and structural induction — which is what lets proofs about all terms run
by induction on term structure (2); the first of the two is also the only
source of a unit law for `~·`, namely `~Δ ≤ Δ`. The closure constant `j`
is co-reflexive, symmetric, co-transitive, and orthogonal to `Δη` (4).

The unit and associativity of substitution are recorded as `Prop` fields
rather than a second `Monoid` instance, which would clash with the one
carrying composition.

## Derived operations

Two operations are `def`s below rather than fields, because their laws
follow from the axioms above:

* `⌃a := Δη ⊔ ~a`, the compatible refinement — the strict one, widened to
  hold on variables;
* `□a := j * a * j`, the closure modality — the pairs of `a` whose two
  endpoints are closed. Its laws are theorems in
  `TRA/Modality.lean`.

One law of `□` does not follow: `(□a)⟦b⟧ ≤ □a`. No condition
on `j` alone yields it through the oplax `subst_compositionality_oplax`,
and the first-order term model of `Instances/PeanoArithmetic`, where `j` is
the identity on closed terms, exhibits a relation and a substituent for
which it fails. The obstruction and the counterexample are recorded in
the *Investigation* block of `TRA/Modality.lean`. It is therefore
absent from the class rather than assumed.

## Derived laws

The section following the class collects the consequences of the axioms
that complete the class's own interface: co-reflexivity of `Δη` and the
full symmetry `Δηᵒ = Δη`, the mirror orthogonality `~a * Δη ≤ ⊥`, the
idempotence `Δη * Δη = Δη`, left and two-argument monotonicity of
substitution, the strictness and binary join laws that follow from
join-preservation, and the corresponding laws of `⌃·` — monotonicity,
multiplicativity `⌃a * ⌃b = ⌃(a * b)`, and converse. They live here
rather than in a file of their own because none of them introduces a new
concept: each one finishes an axiom stated a few lines above. The two
constructions that do introduce concepts, the Howe extension and its
op-Howe mirror, have their own file.

## Naming

Identifiers are used throughout in place of the reference's symbols,
which appear in the thesis text only. Beyond the notations of the
algebraic base (`·ᵒ` for converse, `⇨ₗ` and `⇨ᵣ` for the composition
residuals), this file declares four notations in the `TRA` scope; open
them with `open scoped TRA`. Each prefix binds at `max`, so it takes
exactly the atom that follows: `~(parRed a)` needs its parentheses.

| Reference symbol | Lean name                            | Notation   |
|------------------|--------------------------------------|------------|
| `Δ`              | `(1 : α)`                            | —          |
| `Δη`             | `TRA.varDiag`                        | `Δη`       |
| tilde `a`        | `TRA.scr a`                          | `~a`       |
| hat `a`          | `TRA.cr a`                           | `⌃a`       |
| `a[b]`           | `TRA.subst a b`                      | `a⟦b⟧`     |
| `j` (`□Δ`)       | `TRA.j`                              | —          |
| `□a`             | `TRA.box a`                          | `□a`       |
| `aᴴ`             | `TRA.howe a`                         | `aᴴ`       |
| `b » c`          | `TRA.substResid b c`                 | —          |
| `a§`             | `TRA.opHowe a`                       | `a§`       |
| `♦a`             | `TRA.dia a`                          | `♦a`       |
| `a⇛`             | `LeanTra.Confluence.parRed a`        | `a⇛`       |
| `a∗`             | `LeanTra.Algebra.star a`             | `a∗`       |
| ιa               | `OperationalDecomposition.introduction a`  | `ιa`       |
| ε(a, b)          | `OperationalDecomposition.elimination a b` | `ε(a, b)`  |

Not all of these live in this file. `howe`, `opHowe` and `substResid`
live in `TRA/Howe.lean`; `box` and `dia` in `TRA/Modality.lean`; all
five are scoped in `TRA`. `parRed` is scoped in `LeanTra.Confluence`
(`Confluence/ParallelReduction.lean`); `star` in `LeanTra.Algebra`
(`Algebra/KleeneStar.lean`); `introduction` and `elimination` in
`OperationalDecomposition` (`TRA/OperationalDecomposition.lean`). A
file that wants the last three notations needs the corresponding
`open scoped`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

universe u

open scoped IsInvolutiveQuantale

/-- A `TRA` (Term Relation Algebra) over an involutive unital quantale
`α`. Extends the base (`Monoid` + `CompleteLattice` + `IsQuantale` +
`IsInvolutiveQuantale`) with the variable co-equivalence `Δη`, the strict
compatible refinement `~·`, relation substitution `·⟦·⟧`, and the closure
constant `j`, together with their defining axioms. The closure modality
`□` is derived below as `j * · * j`, and its laws are proved in
`TRA/Modality.lean`. -/
class TRA (α : Type u) [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] where
  /-- The variable co-equivalence `Δη`: the relation that holds between two
  terms exactly when they are the same variable. -/
  varDiag : α
  /-- Strict compatible refinement `~·`: relates two terms built from the same
  outermost operator whose immediate sub-terms are pairwise related. -/
  scr : α → α
  /-- Relation substitution `·⟦·⟧`: `a⟦b⟧` relates two terms obtained from
  `a`-related terms by pointwise `b`-substitution on variables. -/
  subst : α → α → α
  /-- `Δη` is symmetric: swapping the endpoints of a variable-to-variable
  relation stays within the variable relation. -/
  protected varDiag_symmetry : varDiagᵒ ≤ varDiag
  /-- `Δη` is co-transitive: two variables related through an intermediate
  variable are related directly. -/
  protected varDiag_cotransitivity : varDiag ≤ varDiag * varDiag
  /-- `~·` is monotone: refining the argument refines its strict compatible
  refinement. -/
  protected scr_monotonicity ⦃a b : α⦄ : a ≤ b → scr a ≤ scr b
  /-- `~·` preserves composition: relating two terms via a composite of
  sub-term relations is the same as composing their strict refinements. -/
  protected scr_compositionality (a b : α) : scr (a * b) = scr a * scr b
  /-- `~·` preserves converse: turning the sub-term relation around commutes
  with taking the strict compatible refinement. -/
  protected scr_converse_commutation (a : α) : scr (aᵒ) = (scr a)ᵒ
  /-- Variables and compound terms are disjoint: a variable is never a term
  built from an outermost operator, so `Δη` and `~·` cannot both hold. -/
  protected varDiag_scr_orthogonality (a : α) : varDiag * scr a ≤ ⊥
  /-- Substitution is monotone in the second argument: refining the
  substituent refines the result. Left-argument monotonicity follows from
  join-preservation in the first argument (`subst_join_preservation_left`). -/
  protected subst_monotonicity_right ⦃a b b' : α⦄ : b ≤ b' → subst a b ≤ subst a b'
  /-- Substitution is oplax on composition in both arguments: substituting a
  composite is refined by composing the substitutions of its parts. -/
  protected subst_compositionality_oplax (a a' b b' : α) : subst (a * a') (b * b') ≤ subst a b * subst a' b'
  /-- Substitution commutes with converse: swapping the endpoints of a
  substitution is the substitution of the swapped relations. -/
  protected subst_converse_commutation (a b : α) : (subst a b)ᵒ = subst (aᵒ) (bᵒ)
  /-- Substitution preserves arbitrary joins in the first argument:
  substituting into a join of relations is the join of the substituted
  relations. -/
  protected subst_join_preservation_left (s : Set α) (b : α) : subst (sSup s) b = sSup ((fun a => subst a b) '' s)
  /-- `Δη` is a left unit for substitution: substituting into the variable
  relation is the identity. -/
  protected subst_varDiag_unit_left (a : α) : subst varDiag a = a
  /-- `Δη` is a right unit for substitution: substituting variables for
  variables changes nothing. -/
  protected subst_varDiag_unit_right (a : α) : subst a varDiag = a
  /-- Substitution is associative: substituting into a substitution is the
  same as substituting once with the composed substitution. -/
  protected subst_associativity (a b c : α) : subst (subst a b) c = subst a (subst b c)
  /-- Substitution is compatible with term structure, under the guard
  `Δη ≤ b`: `(~a)⟦b⟧ ≤ ~(a⟦b⟧)` whenever the substituent relates every
  variable to itself. The guard is what makes the law provable in models
  with binders: substituting under a binder sends the freshly-bound
  variable to itself, and the pointwise `b`-obligation of relation
  substitution then requires that variable to be `b`-related to itself,
  which the guard supplies. Without the guard the law is refuted in the
  second-order λ-calculus model (see `LambdaCalculus.lean`,
  `not_subst_scr_oplaxity_unguarded`). At first order the guard is
  vacuous — the underlying syntax has no binders — but stating the class
  field with the guard costs nothing there. Every use of this law in the
  abstract development instantiates `b` with a relation containing the
  identity, so the guard is always satisfied at call sites. -/
  protected subst_scr_oplaxity (a b : α) (hb : varDiag ≤ b) : subst (scr a) b ≤ scr (subst a b)
  /-- Fixed-point law for `⌃·`: the identity is a fixed point of compatible
  refinement, i.e. any term equals itself either as a variable or by having
  pairwise equal sub-terms. Stated as `Δη ⊔ ~Δ = Δ` rather than `⌃Δ = Δ`,
  since `⌃·` is defined after the class. -/
  protected cr_fixpoint : varDiag ⊔ scr 1 = 1
  /-- Structural induction: the identity is the *least* fixed point of `⌃·`,
  so any relation stable under compatible refinement contains the identity.
  Stated as `Δη ⊔ ~a ≤ a → Δ ≤ a` rather than `⌃a ≤ a → Δ ≤ a`, since `⌃·`
  is defined after the class. -/
  protected cr_induction ⦃a : α⦄ : varDiag ⊔ scr a ≤ a → 1 ≤ a



  /-- The closure constant `j`: informally the identity restricted to closed
  terms, from which `□a := j * a * j` reads off "the pairs of `a` whose two
  endpoints are closed". Given as a bare element rather than an operation,
  since the whole modal structure is generated by its three co-equivalence
  axioms below plus orthogonality to `Δη`. -/
  j : α
  /-- `j` is co-reflexive: `j ≤ Δ`. Unlike `Δη`, whose co-reflexivity is a
  consequence of the fixed-point law, this is assumed outright: nothing
  else in the class constrains `j` from above. -/
  protected j_coreflexivity : j ≤ 1
  /-- `j` is symmetric: `jᵒ ≤ j`. The full equality `jᵒ = j` is derived
  below (`j_symmetry_eq`) by the same one-line involution argument as
  `varDiag_symmetry_eq`. -/
  protected j_symmetry : jᵒ ≤ j
  /-- `j` is co-transitive: `j ≤ j * j`. Together with the co-reflexivity
  `j ≤ Δ` it forces the reverse `j * j ≤ j` (since `j * j ≤ Δ * j = j`), so
  the equality `j * j = j` holds — `j_idempotence` below. -/
  protected j_cotransitivity : j ≤ j * j
  /-- `j` and `Δη` are orthogonal: `j * Δη ≤ ⊥`. A closed term is never a
  variable. Discharges the derived `box_varDiag_orthogonality : □Δη = ⊥`, via
  `j * Δη * j ≤ ⊥ * j = ⊥`. -/
  protected j_varDiag_orthogonality : j * varDiag ≤ ⊥


namespace TRA

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable [TRA α]



/-! ### Laws of `Δη`

Co-reflexivity is the left half of `cr_fixpoint`. Symmetry is assumed as an
inequality, so that an instance has one direction to prove instead of two;
involutivity supplies the other, and the equality is what `rw` and `simp`
can work with. Idempotence closes `varDiag_cotransitivity` from above. -/

/-- `Δη ≤ Δ`: the variable co-equivalence is co-reflexive. -/
theorem varDiag_coreflexivity : (TRA.varDiag : α) ≤ 1 := le_sup_left.trans_eq TRA.cr_fixpoint

/-- `Δηᵒ = Δη`. The class only assumes `Δηᵒ ≤ Δη`; the reverse inequality is
free, since applying converse-monotonicity to the axiom gives `Δηᵒᵒ ≤ Δηᵒ`,
i.e. `Δη ≤ Δηᵒ`. Stated as an equality so that it can be rewritten with. -/
@[simp] theorem varDiag_symmetry_eq : (TRA.varDiag : α)ᵒ = TRA.varDiag := by
  refine le_antisymm TRA.varDiag_symmetry ?_
  have h : (TRA.varDiag : α)ᵒᵒ ≤ TRA.varDiagᵒ :=
    IsInvolutiveQuantale.converse_monotonicity TRA.varDiag_symmetry
  rwa [IsInvolutiveQuantale.converse_involutivity] at h

/-- `Δη * Δη = Δη`: the variable co-equivalence is idempotent under
composition. -/
@[simp] theorem varDiag_idempotence : (TRA.varDiag : α) * TRA.varDiag = TRA.varDiag := by
  refine le_antisymm ?_ TRA.varDiag_cotransitivity
  calc (TRA.varDiag : α) * TRA.varDiag
      ≤ 1 * TRA.varDiag := mul_le_mul' varDiag_coreflexivity le_rfl
    _ = TRA.varDiag := one_mul _



/-! ### Laws of `~·`

Oplaxity on the unit is the right half of `cr_fixpoint`. Orthogonality to
`Δη` is assumed on one side only; converse gives the mirror. -/

/-- `~Δ ≤ Δ`: the strict compatible refinement is oplax on the unit. -/
theorem scr_unit_oplaxity : TRA.scr (1 : α) ≤ 1 := le_sup_right.trans_eq TRA.cr_fixpoint

/-- Symmetric orthogonality: `~a * Δη ≤ ⊥`, derived from the axiomatic
left-orthogonality via converse. -/
theorem scr_varDiag_orthogonality (a : α) : TRA.scr a * TRA.varDiag ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_monotonicity_iff,
      IsInvolutiveQuantale.converse_bot_strictness,
      IsInvolutiveQuantale.converse_compositionality,
      ← TRA.scr_converse_commutation, varDiag_symmetry_eq]
  exact TRA.varDiag_scr_orthogonality _



/-! ### Compatible refinement -/
/-- Compatible refinement `⌃· := Δη ⊔ ~·`. Derived operation, not a field of
`TRA`: two terms are compatibly refined by `a` when they are either the same
variable or built from the same operator with `a`-related sub-terms. -/
def cr (a : α) : α := varDiag ⊔ scr a

/-- `⌃·` is monotone. -/
theorem cr_monotonicity ⦃a b : α⦄ (h : a ≤ b) : cr a ≤ cr b := sup_le_sup_left (TRA.scr_monotonicity h) _

/-- Fixed-point law for `⌃·`: `⌃Δ = Δ`. -/
@[simp] theorem cr_one : cr (1 : α) = 1 := TRA.cr_fixpoint

/-- Structural induction: `Δ` is the least pre-fixed point of `⌃·`. -/
theorem one_le_of_cr_le ⦃a : α⦄ (h : cr a ≤ a) : 1 ≤ a := TRA.cr_induction h

/-- `⌃·` distributes over composition: `⌃a * ⌃b = ⌃(a * b)`. -/
theorem cr_compositionality (a b : α) : cr a * cr b = cr (a * b) := by
  unfold cr
  rw [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
      Quantale.mul_sup_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_of_le_left varDiag_idempotence.le
    · exact (TRA.varDiag_scr_orthogonality b).trans bot_le
    · exact (scr_varDiag_orthogonality a).trans bot_le
    · rw [TRA.scr_compositionality]; exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_sup_of_le_left (le_sup_of_le_left TRA.varDiag_cotransitivity)
    · rw [TRA.scr_compositionality]
      exact le_sup_of_le_right (le_sup_of_le_right le_rfl)

/-- `⌃·` commutes with converse: `(⌃a)ᵒ = ⌃(aᵒ)`. -/
@[simp]
theorem cr_converse_commutation (a : α) : (cr a)ᵒ = cr (aᵒ) := by
  unfold cr
  rw [IsInvolutiveQuantale.converse_join_preservation_binary, varDiag_symmetry_eq, ← TRA.scr_converse_commutation]



/-! ### Laws of `·⟦·⟧`

The first three come from `subst_join_preservation_left`, instantiated at
the empty set and, twice, at a two-element set. The last combines the
recovered left monotonicity with the axiom `subst_monotonicity_right`. -/

/-- Substitution annihilates `⊥` on the left: `⊥⟦b⟧ = ⊥`. -/
@[simp]
theorem subst_bot_strictness_left (b : α) : TRA.subst ⊥ b = ⊥ := by
  have h := TRA.subst_join_preservation_left (∅ : Set α) b
  simp only [Set.image_empty, sSup_empty] at h
  exact h

/-- Substitution preserves binary joins in the first argument. -/
theorem subst_join_preservation_binary_left (a a' b : α) :
    TRA.subst (a ⊔ a') b = TRA.subst a b ⊔ TRA.subst a' b := by
  have h := TRA.subst_join_preservation_left ({a, a'} : Set α) b
  simp only [sSup_pair, Set.image_pair] at h
  exact h

/-- Left-argument monotonicity of substitution. -/
theorem subst_monotonicity_left ⦃a a' b : α⦄ (h : a ≤ a') : TRA.subst a b ≤ TRA.subst a' b := by
  have key : TRA.subst (sSup ({a, a'} : Set α)) b
      = sSup ((fun x => TRA.subst x b) '' ({a, a'} : Set α)) :=
    TRA.subst_join_preservation_left _ _
  rw [sSup_pair, Set.image_pair, sSup_pair, sup_eq_right.mpr h] at key
  have hle : TRA.subst a b ≤ TRA.subst a b ⊔ TRA.subst a' b := le_sup_left
  rw [← key] at hle
  exact hle

/-- Full two-argument monotonicity of substitution. -/
theorem subst_monotonicity ⦃a a' b b' : α⦄ (ha : a ≤ a') (hb : b ≤ b') : TRA.subst a b ≤ TRA.subst a' b' :=
  (subst_monotonicity_left ha).trans (TRA.subst_monotonicity_right hb)

/-- Substituting into a compatible refinement: `(⌃a)⟦b⟧ ≤ b ⊔ ⌃(a⟦b⟧)`,
under the guard `Δη ≤ b`. Inherits the guard from
`TRA.subst_scr_oplaxity`. -/
theorem subst_cr_oplaxity (a b : α) (hb : TRA.varDiag ≤ b) :
    TRA.subst (TRA.cr a) b ≤ b ⊔ TRA.cr (TRA.subst a b) := by
  unfold TRA.cr
  rw [subst_join_preservation_binary_left, TRA.subst_varDiag_unit_left]
  exact sup_le_sup_left ((TRA.subst_scr_oplaxity _ _ hb).trans le_sup_right) b

/-- Converse commutes with the base instance: `(a⟦Δ⟧)ᵒ = aᵒ⟦Δ⟧`. -/
theorem subst_one_converse_commutation (a : α) :
    (TRA.subst a 1)ᵒ = TRA.subst aᵒ 1 := by
  rw [TRA.subst_converse_commutation, IsInvolutiveQuantale.converse_one]



/-! ### Laws of `j`

The same two upgrades that `Δη` gets above. Co-transitivity becomes
idempotence once co-reflexivity closes it from above; the assumed
inequality `jᵒ ≤ j` becomes an equality by involutivity, which is the
form `rw` and `simp` can use. Both are consumed by the modality derived
from `j` below. -/

/-- `j * j = j`. `≤` from `j_coreflexivity` (`j*j ≤ 1*j = j`); `≥` is
`j_cotransitivity`. -/
@[simp] theorem j_idempotence : (TRA.j : α) * TRA.j = TRA.j := by
  refine le_antisymm ?_ TRA.j_cotransitivity
  calc (TRA.j : α) * TRA.j
      ≤ 1 * TRA.j := mul_le_mul' TRA.j_coreflexivity le_rfl
    _ = TRA.j := one_mul _

/-- `jᵒ = j`: same one-liner as `varDiag_symmetry_eq`, from `j_symmetry`
plus involutivity of converse. -/
@[simp] theorem j_symmetry_eq : (TRA.j : α)ᵒ = TRA.j := by
  refine le_antisymm TRA.j_symmetry ?_
  have h : (TRA.j : α)ᵒᵒ ≤ (TRA.j : α)ᵒ :=
    IsInvolutiveQuantale.converse_monotonicity TRA.j_symmetry
  rwa [IsInvolutiveQuantale.converse_involutivity] at h


/-! ### Notation -/

@[inherit_doc] scoped prefix:max "~" => TRA.scr
@[inherit_doc] scoped prefix:max "⌃" => TRA.cr
@[inherit_doc] scoped notation:max a "⟦" b "⟧" => TRA.subst a b
@[inherit_doc] scoped notation:max "Δη" => TRA.varDiag
/-- `Δ` is the identity relation, i.e. the unit `1` of the quantale. -/
scoped notation:max "Δ" => (1 : _)

end TRA
