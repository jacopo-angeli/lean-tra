/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic

/-!
# Reductions

The `IsReduction` predicate, isolating the standing hypothesis
`Δη * a = ⊥` — the LHS of a rule is never a variable
(Gavazzo LICS'23 Remark 5 / LICS'26 Def. 17).
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-- `a` is a *reduction* when its LHS is never a variable: `Δη * a = ⊥`.
Gavazzo LICS'23 Remark 5 / LICS'26 Def. 17. -/
def IsReduction (a : α) : Prop := SRA.varDiag * a = ⊥

end LeanTra.Confluence
