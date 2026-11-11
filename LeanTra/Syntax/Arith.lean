/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Syntax of Peano arithmetic

Terms of Peano arithmetic (`zero`, `succ`, `plus`, `mult`) over a context given by a type,
with simultaneous substitution and renaming.

## Main definitions

* `LeanTra.Instances.PeanoArithmetic.Tm Γ`: terms with variables in `Γ`.
* `Tm.subst`, `Tm.ren`: simultaneous substitution and renaming.
* `Subst.id`, `Subst.comp`: identity and composition of substitutions.
* `ClosedTm`: closed terms, `Tm Empty`.
* `Tm.close`: weakening of a closed term to any context.

## Main statements

* `Tm.subst_id`, `Tm.subst_comp`: unit and associativity laws of substitution.
* `Tm.ren_id`, `Tm.ren_ren`: renaming is functorial.
* `Tm.subst_ren`, `Tm.ren_subst`: renaming and substitution commute.
* `Subst.comp_assoc`, `Subst.id_comp`, `Subst.comp_id`: substitutions compose associatively,
  with `Subst.id` as unit.
* `Tm.ren_injective`: renaming along an injective map is injective.

## Implementation notes

Contexts are types rather than finite sets of names, so renamings and substitutions are plain
functions and no α-conversion is needed.
-/

@[expose] public section

namespace LeanTra.Instances.PeanoArithmetic

/-!
We start from the bottom of the layer cake: the inductive datatype of
Peano terms in an arbitrary type-valued context, and the substitution
and renaming operations on it. Nothing here is Peano-specific in a deep
sense — the same construction goes through for any first-order
signature — but every downstream section depends on having these
definitions and their monad laws in place. A context Γ is a type, not
a finite subset of a name universe: renamings `Γ → Δ` and substitutions
`Γ → Tm Δ` are then plain functions, α-issues disappear, and the
weakening of a term into a larger context is transported by an
explicit `Tm.ren`. The three lemmas `subst_id`, `subst_comp`, and their
counterparts for renaming are the equational content of the Kleisli
monad `Γ ↦ Tm Γ`, and are the *only* piece of syntactic reasoning that
`subst_associativity` will need much later.
-/

/-- The terms of Peano arithmetic: a variable, the constant zero, a
successor node, a plus node, or a mult node. -/
inductive Tm (Γ : Type) where
  /-- A variable term. -/
  | var  : Γ → Tm Γ
  /-- Nullary zero constant. -/
  | zero : Tm Γ
  /-- Unary successor: `succ(x)`. -/
  | succ : Tm Γ → Tm Γ
  /-- Binary plus: `plus(m, n)`, with `m` the eagerly-evaluated major
  argument. -/
  | plus : Tm Γ → Tm Γ → Tm Γ
  /-- Binary mult: `mult(m, n)`, with `m` the eagerly-evaluated major
  argument. -/
  | mult : Tm Γ → Tm Γ → Tm Γ

namespace Tm

variable {Γ Δ E : Type}

/-- Simultaneous capture-free substitution: `t.subst τ` replaces every
variable `x : Γ` in `t` by `τ x : Tm Δ`. Since contexts are types and
variables have no binding structure, there is no capture to avoid. -/
def subst : Tm Γ → (Γ → Tm Δ) → Tm Δ
  | var x,     τ => τ x
  | zero,      _ => zero
  | succ t,    τ => succ (t.subst τ)
  | plus m n,  τ => plus (m.subst τ) (n.subst τ)
  | mult m n,  τ => mult (m.subst τ) (n.subst τ)

/-- Renaming: substitution whose targets are variables. -/
def ren (t : Tm Γ) (f : Γ → Δ) : Tm Δ := t.subst (Tm.var ∘ f)

end Tm

namespace Subst

variable {Γ Δ E : Type}

/-- The identity substitution `Γ → Tm Γ`. -/
def id : Γ → Tm Γ := Tm.var

/-- Kleisli composition of substitutions. -/
def comp (τ : Γ → Tm Δ) (θ : Δ → Tm E) : Γ → Tm E :=
  fun x => (τ x).subst θ

end Subst

namespace Tm

variable {Γ Δ E Z : Type}

/-!
The following simp lemmas commute `subst` and `ren` with each
constructor of `Tm`. They are all definitional but need to be tagged
`@[simp]` so that `simp` can push substitutions and renamings through
compound terms automatically in every downstream proof.
-/

@[simp] theorem subst_var (x : Γ) (τ : Γ → Tm Δ) : (var x).subst τ = τ x := rfl

@[simp] theorem subst_zero (τ : Γ → Tm Δ) : (zero : Tm Γ).subst τ = zero := rfl

@[simp] theorem subst_succ (t : Tm Γ) (τ : Γ → Tm Δ) :
    (succ t).subst τ = succ (t.subst τ) := rfl

@[simp] theorem subst_plus (m n : Tm Γ) (τ : Γ → Tm Δ) :
    (plus m n).subst τ = plus (m.subst τ) (n.subst τ) := rfl

@[simp] theorem subst_mult (m n : Tm Γ) (τ : Γ → Tm Δ) :
    (mult m n).subst τ = mult (m.subst τ) (n.subst τ) := rfl

@[simp] theorem ren_var (x : Γ) (f : Γ → Δ) : (var x : Tm Γ).ren f = var (f x) := rfl

@[simp] theorem ren_zero (f : Γ → Δ) : (zero : Tm Γ).ren f = zero := rfl

@[simp] theorem ren_succ (t : Tm Γ) (f : Γ → Δ) :
    (succ t).ren f = succ (t.ren f) := rfl

@[simp] theorem ren_plus (m n : Tm Γ) (f : Γ → Δ) :
    (plus m n).ren f = plus (m.ren f) (n.ren f) := rfl

@[simp] theorem ren_mult (m n : Tm Γ) (f : Γ → Δ) :
    (mult m n).ren f = mult (m.ren f) (n.ren f) := rfl

/-!
The monad laws for `subst` and `ren`, plus their interaction (a
substitution after a renaming factors through the pre-composed
substitution, and dually). Each proof is an induction on `t` with one
case per constructor; the boilerplate is unavoidable and will be
invoked implicitly by every downstream proof that manipulates
substitutions.
-/

/-- The identity substitution is a right identity for `subst`. -/
theorem subst_id (t : Tm Γ) : t.subst Subst.id = t := by
  induction t with
  | var x    => rfl
  | zero     => rfl
  | succ t ih => simp [Tm.subst, ih]
  | plus m n ihm ihn => simp [Tm.subst, ihm, ihn]
  | mult m n ihm ihn => simp [Tm.subst, ihm, ihn]

/-- Substitution respects Kleisli composition. -/
theorem subst_comp (t : Tm Γ) (τ : Γ → Tm Δ) (θ : Δ → Tm E) :
    (t.subst τ).subst θ = t.subst (Subst.comp τ θ) := by
  induction t with
  | var x    => rfl
  | zero     => rfl
  | succ t ih => simp [Tm.subst, ih]
  | plus m n ihm ihn => simp [Tm.subst, ihm, ihn]
  | mult m n ihm ihn => simp [Tm.subst, ihm, ihn]

/-- Substitution after a renaming. -/
theorem subst_ren (t : Tm Γ) (f : Γ → Δ) (τ : Δ → Tm E) :
    (t.ren f).subst τ = t.subst (τ ∘ f) := by
  unfold ren; rw [subst_comp]; rfl

/-- Renaming after a substitution. -/
theorem ren_subst (t : Tm Γ) (τ : Γ → Tm Δ) (g : Δ → E) :
    (t.subst τ).ren g = t.subst (fun x => (τ x).ren g) := by
  unfold ren; rw [subst_comp]; rfl

/-- Composition of renamings. -/
theorem ren_ren (t : Tm Γ) (f : Γ → Δ) (g : Δ → E) :
    (t.ren f).ren g = t.ren (g ∘ f) := by
  unfold ren; rw [subst_comp]; rfl

/-- The identity renaming is the identity. -/
theorem ren_id (t : Tm Γ) : t.ren _root_.id = t := by
  unfold ren; change t.subst (fun x => Tm.var x) = t; exact subst_id t

/-- On an empty context, substitution is invariant in its substitution
argument. -/
theorem subst_empty [IsEmpty Γ] (t : Tm Γ) (τ₁ τ₂ : Γ → Tm Δ) :
    t.subst τ₁ = t.subst τ₂ := by
  induction t with
  | var x => exact isEmptyElim x
  | zero => rfl
  | succ t ih => simp [Tm.subst, ih]
  | plus m n ihm ihn => simp [Tm.subst, ihm, ihn]
  | mult m n ihm ihn => simp [Tm.subst, ihm, ihn]

/-- Injectivity of renaming. -/
theorem ren_injective (f : Γ → Δ) (hf : Function.Injective f) :
    Function.Injective (fun t : Tm Γ => t.ren f) := by
  intro t
  induction t with
  | var x =>
    intro s h
    cases s with
    | var y   => exact congrArg Tm.var (hf (Tm.var.inj h))
    | zero    => cases h
    | succ _  => cases h
    | plus _ _ => cases h
    | mult _ _ => cases h
  | zero =>
    intro s h
    cases s with
    | var _   => cases h
    | zero    => rfl
    | succ _  => cases h
    | plus _ _ => cases h
    | mult _ _ => cases h
  | succ t ih =>
    intro s h
    cases s with
    | var _    => cases h
    | zero     => cases h
    | succ s'  => exact congrArg Tm.succ (ih (Tm.succ.inj h))
    | plus _ _ => cases h
    | mult _ _ => cases h
  | plus m n ihm ihn =>
    intro s h
    cases s with
    | var _    => cases h
    | zero     => cases h
    | succ _   => cases h
    | plus m' n' =>
      obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp h
      exact congrArg₂ Tm.plus (ihm hm) (ihn hn)
    | mult _ _ => cases h
  | mult m n ihm ihn =>
    intro s h
    cases s with
    | var _    => cases h
    | zero     => cases h
    | succ _   => cases h
    | plus _ _ => cases h
    | mult m' n' =>
      obtain ⟨hm, hn⟩ := Tm.mult.injEq _ _ _ _ |>.mp h
      exact congrArg₂ Tm.mult (ihm hm) (ihn hn)

end Tm

namespace Subst

variable {Γ Δ E Z : Type}

theorem comp_assoc (τ : Γ → Tm Δ) (θ : Δ → Tm E) (κ : E → Tm Z) :
    comp (comp τ θ) κ = comp τ (comp θ κ) := by
  funext x
  change ((τ x).subst θ).subst κ = (τ x).subst (comp θ κ)
  exact Tm.subst_comp (τ x) θ κ

theorem id_comp (τ : Γ → Tm Δ) : comp Subst.id τ = τ := by funext x; rfl

theorem comp_id (τ : Γ → Tm Δ) : comp τ Subst.id = τ := by
  funext x; change (τ x).subst Subst.id = τ x; exact Tm.subst_id (τ x)

end Subst

/-!
A closed term is a term with no free variables, i.e. a term at the
empty context: `ClosedTm := Tm Empty`. Every closed term embeds into
an arbitrary context via the unique function `Empty.elim : Empty → Γ`,
and substitution or renaming acts trivially on any term in the image
of this embedding. The `close` operation and its two invariance lemmas
below package this fact for later use; they will be needed in
`box_elimination_oplaxity` and in the definition of `j`.
-/

/-- Closed terms: the empty-context fibre. -/
abbrev ClosedTm := Tm Empty

namespace Tm

variable {Γ Δ : Type}

/-- Weakening of a closed term into an arbitrary context. -/
def close (Γ : Type) (t : ClosedTm) : Tm Γ := t.ren Empty.elim

/-- Substitution acts trivially on a weakened closed term. -/
theorem subst_close (Γ Δ : Type) (t : ClosedTm) (τ : Γ → Tm Δ) :
    (close Γ t).subst τ = close Δ t := by
  unfold close ren
  rw [subst_comp]
  apply congrArg t.subst
  funext e; exact e.elim

/-- Renaming acts trivially on a weakened closed term. -/
theorem ren_close (Γ Δ : Type) (t : ClosedTm) (f : Γ → Δ) :
    (close Γ t).ren f = close Δ t := by
  unfold ren; exact subst_close Γ Δ t (Tm.var ∘ f)

end Tm

end LeanTra.Instances.PeanoArithmetic
