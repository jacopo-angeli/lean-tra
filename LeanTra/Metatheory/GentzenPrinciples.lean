/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.OperationalDecomposition

/-!
# Gentzen inversion and conservation principles

The declarations in this file are properties a relation may or may not
have. They are not part of the algebraic structure: they are the
hypotheses under which the metatheorems hold, and they are collected
here because all three concern the same question, namely when a rule of
computation is permitted to fire and how firing interacts with
substitution.

Confluence of orthogonal reduction is established from two conditions,
of which the second mentions parallel reduction. Parallel reduction is a
construction on the rule, not a property of it, so verifying that
condition requires reasoning about the very object whose behaviour is
being established. The condition is therefore not local.

The principles below replace it. Each is an inequality on the rule
alone, and together they entail the non-local condition, so that
confluence follows from hypotheses that can be checked on a rule by
inspection.

A destructor is bound to inspect one of its arguments before it can act.
Gentzen's Inversion Principle says that a rule fires only once that
argument holds a constructor: in the lambda calculus, beta may contract
app(t, s) only when t is already a lambda, never when it is a
variable or an application still to be evaluated. Algebraically this
becomes a factorisation: every step of the rule passes through an
elimination form whose inspected slot holds an introduction form.

The Conservation Principle concerns what happens when the rule does
fire. Firing consumes a construction, and the arguments of that
construction are substituted into its body; the principle says that the
two operations commute. Take two beta redexes related argument by
argument, say (λx.p)w and (λx.u)v with the bodies related and the
operands related. Contracting gives p[w/x] and u[v/x], and these are
again related, by the relation substituted into itself. So the behaviour
of the rule depends only on the outermost operator of the term and on
the outermost shape of its operands, and is parametric in everything
below. This is the algebraic form of what proof theory calls harmony.

The closed inversion principle strengthens the first one. It asks that
the inspected slot hold not merely a constructor but a value, that is a
closed one: beta may contract app(λx.x, s) but not app(λx.y, s) with
y free.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.* LICS 2026.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA

open OperationalDecomposition

namespace LeanTra.Metatheory

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [OperationalDecomposition α]



/-! ### Compatibility

A relation is compatible when it is closed under term formation. The
conservation principle is stated for every such relation, and it is the
only place the notion is used. -/

/-- `x` is compatible when `⌃x ≤ x`. -/
def IsCompatible (x : α) : Prop := ⌃x ≤ x



/-! ### The principles

Both are inequalities in the rule `a` alone. Inversion constrains where a
step may occur — on the left, through an elimination whose major slot is
an introduction form. Conservation constrains what a step produces — on
the right, through the substitution of a compatible relation into
itself. -/

/-- Gentzen's inversion principle: every `a`-step factors on the left
through an elimination with an introduction form in the major slot. -/
def GIP (a : α) : Prop := a ≤ ε(ι Δ, Δ) * a

/-- Gentzen's conservation principle: for every compatible `x`, a step
after `ε(⌃x, x)` factors on the right through `x⟦x⟧` after the step. -/
def GCP (a : α) : Prop := ∀ x, IsCompatible x → ε(⌃x, x) * a ≤ a * x⟦x⟧




end LeanTra.Metatheory
