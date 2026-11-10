/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Syntax of the untyped λ-calculus

Well-scoped terms of the untyped λ-calculus in de Bruijn notation, with
renaming and simultaneous substitution.

## Main definitions

* `LeanTra.Instances.Lambda.Lam n`: λ-terms with free variables in `Fin n`.
* `Lam.ren`, `Lam.subst`: renaming and simultaneous substitution.
* `Lam.liftRen`, `Lam.liftSubst`: extension of a renaming or a substitution under a binder.
* `Lam.subst0`: substitution for the variable of index `0`, as in β-reduction.
* `Lam.close`: weakening of a closed term to any context.

## Main statements

* `Lam.ren_ren`, `Lam.ren_id`: renaming is functorial.
* `Lam.subst_ren`, `Lam.ren_subst`: renaming and substitution commute.
* `Lam.subst_id`, `Lam.subst_comp`: unit and associativity laws of substitution.

## Implementation notes

Indexing terms by the number of free variables makes α-equivalent terms equal,
so no freshness reasoning is needed.
-/

@[expose] public section

namespace LeanTra.Instances.Lambda

/-! ## Section 1: Terms

The first task is to fix a syntax. We choose a well-scoped de Bruijn
presentation, indexing terms by the number of free variables available
to them (`Lam n`). This choice is deliberate: by turning the binding
discipline into an arithmetic on natural numbers we make α-equivalence
*definitional* (two terms are equal iff their underlying trees are
equal) and avoid ever having to reason about freshness of names. -/

/-- Well-scoped untyped λ-terms with `n` free variables. -/
inductive Lam : Nat → Type where
  /-- A variable, given by its de Bruijn index. -/
  | var : {n : Nat} → Fin n → Lam n
  /-- Application. -/
  | app : {n : Nat} → Lam n → Lam n → Lam n
  /-- Abstraction: binds one variable, incrementing the arity. -/
  | lam : {n : Nat} → Lam (n + 1) → Lam n

namespace Lam

variable {n m k : Nat}

/-! ### Lifted maps at binders

The price of the de Bruijn presentation is that renamings and
substitutions must be lifted explicitly whenever they cross a binder,
and this is what `liftRen` and `liftSubst` do. Once these lifts are in
place, the whole equational theory of substitution developed below
reduces to a handful of lift-commutation lemmas (`liftRen_comp`,
`liftSubst_liftRen`, `liftRen_liftSubst`, `liftSubst_comp`) that
thread the routine inductions through their `lam` cases; a nominal
presentation would finesse this bookkeeping at the cost of dragging in
an infrastructure of finitely-supported sets that is a development
project in its own right. Every equational-theory proof further down
in the section goes by induction on the term with the target arity
generalised, so that the `lam` case has the right induction hypothesis
available.

Concretely, `liftRen` sends the freshly-bound index (`Fin.mk 0`) to
itself and shifts all other images by `Fin.succ`; `liftSubst` does the
same for substitutions, weakening each image by `Fin.succ`. Both are
used uniformly in the `lam` cases of `ren` and `subst` respectively. -/

/-- Lift a renaming across one binder. -/
def liftRen (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

/-- Capture-free renaming: transport free variables along `f`,
propagating through binders via `liftRen`. -/
def ren : {n m : Nat} → Lam n → (Fin n → Fin m) → Lam m
  | _, _, var x,    f => var (f x)
  | _, _, app t s,  f => app (t.ren f) (s.ren f)
  | _, _, lam t,    f => lam (t.ren (liftRen f))

/-- Lift a substitution across one binder: the fresh index becomes
`var 0`, the images of the old variables are shifted into the extended
context by `Fin.succ`. -/
def liftSubst (τ : Fin n → Lam m) : Fin (n + 1) → Lam (m + 1) :=
  Fin.cases (var 0) (fun i => (τ i).ren Fin.succ)

/-- Capture-avoiding simultaneous substitution. -/
def subst : {n m : Nat} → Lam n → (Fin n → Lam m) → Lam m
  | _, _, var x,    τ => τ x
  | _, _, app t s,  τ => app (t.subst τ) (s.subst τ)
  | _, _, lam t,    τ => lam (t.subst (liftSubst τ))

/-! ### Reduction lemmas, the `simp`-normal shapes

The six lemmas below simply restate the defining equations of `ren`
and `subst` as named theorems, one per constructor of `Lam`. Their
proof is `rfl` in every case, so mathematically they add nothing;
their purpose is to be picked up by Lean's rewrite tactic `simp`,
which uses them as automatic rewrite rules. From that point on, any
proof that traverses a term will canonicalise expressions like
`(app t s).ren f` into `app (t.ren f) (s.ren f)` without our having
to unfold the definition of `ren` by hand every time. This is the
standard Lean idiom for exposing the computational content of a
recursive definition to the proof automation. -/

/-- `simp`-normal shape of `ren` on a variable. -/
@[simp] theorem ren_var (x : Fin n) (f : Fin n → Fin m) :
    (var x : Lam n).ren f = var (f x) := rfl

/-- `simp`-normal shape of `ren` on `app`. -/
@[simp] theorem ren_app (t s : Lam n) (f : Fin n → Fin m) :
    (app t s).ren f = app (t.ren f) (s.ren f) := rfl

/-- `simp`-normal shape of `ren` on `lam`; the recursive call uses `liftRen`. -/
@[simp] theorem ren_lam (t : Lam (n + 1)) (f : Fin n → Fin m) :
    (lam t).ren f = lam (t.ren (liftRen f)) := rfl

/-- `simp`-normal shape of `subst` on a variable. -/
@[simp] theorem subst_var (x : Fin n) (τ : Fin n → Lam m) :
    (var x : Lam n).subst τ = τ x := rfl

/-- `simp`-normal shape of `subst` on `app`. -/
@[simp] theorem subst_app (t s : Lam n) (τ : Fin n → Lam m) :
    (app t s).subst τ = app (t.subst τ) (s.subst τ) := rfl

/-- `simp`-normal shape of `subst` on `lam`; the recursive call uses `liftSubst`. -/
@[simp] theorem subst_lam (t : Lam (n + 1)) (τ : Fin n → Lam m) :
    (lam t).subst τ = lam (t.subst (liftSubst τ)) := rfl

/-! ### Equational theory of `ren` and `subst`

This is the section that turns the two recursive definitions above
into a genuine algebra of substitution. What lives here is the
standard package of laws every substitution operation must satisfy:
composition of renamings (`ren_ren`), identity renaming (`ren_id`),
the two mixed laws relating renaming and substitution (`subst_ren`,
`ren_subst`), the fact that variables act as a right unit
(`subst_id`), and Kleisli associativity of substitution
(`subst_comp`). Downstream everything, from the TRA axioms in
Section 3 to the five rule-level conditions on β in Section 4, is
proved by unfolding definitions with `simp` and rewriting along these
six laws; without them we would have to re-do the `lam`-case
gymnastics every single time. -/

/-- Functoriality of `liftRen`: composing two renaming lifts equals the lift
of the composite. Threaded through the `lam` case of `ren_ren`. -/
theorem liftRen_comp (f : Fin n → Fin m) (g : Fin m → Fin k)
    (i : Fin (n + 1)) :
    liftRen g (liftRen f i) = liftRen (fun x => g (f x)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

/-- Commutation of `liftSubst` and `liftRen`: precomposing a lifted
substitution by a lifted renaming equals lifting the precomposed
substitution. Threaded through the `lam` case of `subst_ren`. -/
theorem liftSubst_liftRen (f : Fin n → Fin m) (τ : Fin m → Lam k)
    (i : Fin (n + 1)) :
    liftSubst τ (liftRen f i) = liftSubst (fun x => τ (f x)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

/-- Composition of renamings: `(t.ren f).ren g = t.ren (g ∘ f)`. -/
theorem ren_ren : ∀ {n m k : Nat} (t : Lam n) (f : Fin n → Fin m) (g : Fin m → Fin k),
    (t.ren f).ren g = t.ren (fun x => g (f x)) := by
  intro n m k t
  induction t generalizing m k with
  | var x => intros; rfl
  | app t s ih_t ih_s =>
    intro f g
    simp only [ren_app, ih_t, ih_s]
  | lam t ih =>
    intro f g
    simp only [ren_lam]
    have hmap : (fun i => liftRen g (liftRen f i)) = liftRen (fun x => g (f x)) := by
      funext i; exact liftRen_comp f g i
    rw [ih, hmap]

/-- The identity renaming is the identity. -/
theorem ren_id : ∀ {n : Nat} (t : Lam n), t.ren (fun x => x) = t := by
  intro n t
  induction t with
  | var x => rfl
  | app t s ih_t ih_s => simp only [ren_app, ih_t, ih_s]
  | @lam k t ih =>
    change Lam.lam (t.ren (liftRen (fun x => x))) = Lam.lam t
    have h : liftRen (fun x : Fin k => x) = fun x => x := by
      funext i; refine Fin.cases rfl (fun _ => rfl) i
    rw [h]
    exact congrArg Lam.lam ih

/-- Substitution after a renaming: `(t.ren f).subst τ = t.subst (τ ∘ f)`. -/
theorem subst_ren : ∀ {n m k : Nat} (t : Lam n) (f : Fin n → Fin m)
    (τ : Fin m → Lam k),
    (t.ren f).subst τ = t.subst (fun x => τ (f x)) := by
  intro n m k t
  induction t generalizing m k with
  | var x => intros; rfl
  | app t s ih_t ih_s =>
    intro f τ
    simp only [ren_app, subst_app, ih_t, ih_s]
  | lam t ih =>
    intro f τ
    simp only [ren_lam, subst_lam]
    have hmap : (fun i => liftSubst τ (liftRen f i))
                = liftSubst (fun x => τ (f x)) := by
      funext i; exact liftSubst_liftRen f τ i
    rw [ih, hmap]

/-- The `ren` counterpart of `liftSubst`-`Fin.succ` swap needed in
`ren_subst`'s `lam` case. -/
theorem liftRen_liftSubst (τ : Fin n → Lam m) (g : Fin m → Fin k)
    (i : Fin (n + 1)) :
    (liftSubst τ i).ren (liftRen g)
      = liftSubst (fun x => (τ x).ren g) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    change ((τ j).ren Fin.succ).ren (liftRen g)
        = ((τ j).ren g).ren Fin.succ
    rw [ren_ren, ren_ren]
    congr 1

/-- Renaming after a substitution: an outer renaming distributes into
the substitution as a post-composed renaming, everywhere. -/
theorem ren_subst : ∀ {n m k : Nat} (t : Lam n) (τ : Fin n → Lam m)
    (g : Fin m → Fin k),
    (t.subst τ).ren g = t.subst (fun x => (τ x).ren g) := by
  intro n m k t
  induction t generalizing m k with
  | var x => intros; rfl
  | app t s ih_t ih_s =>
    intro τ g
    simp only [subst_app, ren_app, ih_t, ih_s]
  | lam t ih =>
    intro τ g
    simp only [subst_lam, ren_lam]
    have hmap : (fun x => (liftSubst τ x).ren (liftRen g))
                = liftSubst (fun x => (τ x).ren g) := by
      funext i; exact liftRen_liftSubst τ g i
    rw [ih, hmap]

/-- The `subst` counterpart of the lift-composition lemma used in
`subst_comp`'s `lam` case. -/
theorem liftSubst_comp (τ : Fin n → Lam m) (θ : Fin m → Lam k)
    (i : Fin (n + 1)) :
    (liftSubst τ i).subst (liftSubst θ)
      = liftSubst (fun x => (τ x).subst θ) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    change ((τ j).ren Fin.succ).subst (liftSubst θ)
        = ((τ j).subst θ).ren Fin.succ
    rw [subst_ren, ren_subst]
    rfl

/-- The identity substitution `var` is a right unit for `subst`. -/
theorem subst_id : ∀ {n : Nat} (t : Lam n), t.subst var = t := by
  intro n t
  induction t with
  | var x => rfl
  | app t s ih_t ih_s => simp only [subst_app, ih_t, ih_s]
  | @lam k t ih =>
    change Lam.lam (t.subst (liftSubst Lam.var)) = Lam.lam t
    have h : liftSubst (Lam.var : Fin k → Lam k) = Lam.var := by
      funext i; refine Fin.cases rfl (fun _ => rfl) i
    rw [h]
    exact congrArg Lam.lam ih

/-- Kleisli associativity of substitution. -/
theorem subst_comp : ∀ {n m k : Nat} (t : Lam n) (τ : Fin n → Lam m)
    (θ : Fin m → Lam k),
    (t.subst τ).subst θ = t.subst (fun x => (τ x).subst θ) := by
  intro n m k t
  induction t generalizing m k with
  | var x => intros; rfl
  | app t s ih_t ih_s =>
    intro τ θ
    simp only [subst_app, ih_t, ih_s]
  | lam t ih =>
    intro τ θ
    simp only [subst_lam]
    have hmap : (fun i => (liftSubst τ i).subst (liftSubst θ))
                = liftSubst (fun x => (τ x).subst θ) := by
      funext i; exact liftSubst_comp τ θ i
    rw [ih, hmap]

/-! ### Derived operations: `subst0` and `close`

Two specialisations of `subst` and `ren` are singled out because they
are the exact shapes the later sections consume. `subst0` is the
one-variable substitution that gives β-reduction its right-hand side:
the β-rule of Section 4 will read `app (lam t) s ↦ subst0 t s`, so
this operation is not a piece of general infrastructure but the actual
substitution shape of the calculus we are formalising. `close` goes
the other way: it takes a term with no free variables (`Lam 0`) and
injects it into an arbitrary context by weakening along the empty
renaming `Fin 0 → Fin n`, together with the small lemma `ren_close`
saying that further renamings act trivially on such an injection.
Closed terms and their weakening are what the closed-value modality
`j` of Section 3 picks up, so this pair of definitions is the concrete
raw material on which two of the TRA operations of the file will be
built. -/

/-- Single-variable substitution: replace `Fin 0` in `t` by `s`. -/
def subst0 (t : Lam (n + 1)) (s : Lam n) : Lam n :=
  t.subst (Fin.cases s var)

/-- Weakening of a closed term into arity `n`. -/
def close (n : Nat) (t : Lam 0) : Lam n := t.ren (Fin.elim0)

/-- Renaming acts trivially on a weakened closed term. -/
theorem ren_close (n m : Nat) (t : Lam 0) (f : Fin n → Fin m) :
    (close n t).ren f = close m t := by
  unfold close
  rw [ren_ren]
  congr 1
  funext i
  exact i.elim0

end Lam

end LeanTra.Instances.Lambda
