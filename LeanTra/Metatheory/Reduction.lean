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

end LeanTra.Confluence
