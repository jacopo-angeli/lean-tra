/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic

/-!
# Reductions

The `IsReduction` predicate, isolating the standing hypothesis
`Δη * a = ⊥` — the LHS of a rule is never a variable. Consumed downstream
as the standing assumption on rewrite rules.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Definition 17.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-- `a` is a *reduction* when its LHS is never a variable: `Δη * a = ⊥`. -/
def IsReduction (a : α) : Prop := SRA.varDiag * a = ⊥

/-- A relation `x` is *compatible* when the compatible refinement of `x`
refines `x`: `hat x ≤ x`. -/
def IsCompatible (x : α) : Prop := SRA.cr x ≤ x

/-- A relation `a` is *substitutive* when substituting `a`-related terms
into an `a`-related term stays `a`-related: `a[a] ≤ a`. -/
def IsSubstitutive (a : α) : Prop := SRA.subst a a ≤ a

/-- A reduction `a` is *deterministic* when its base substitution instance
`a[Δ]` satisfies `a[Δ]° * a[Δ] ≤ Δ`; the two ends of a rewrite of the same
term agree up to renaming. This is the paper's first orthogonality
condition. -/
def IsDeterministicReduction (a : α) : Prop :=
  (SRA.subst a 1)ᵒ * SRA.subst a 1 ≤ 1

end LeanTra.Confluence
