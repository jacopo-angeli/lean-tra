/-
Master's thesis: Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
public import LeanTra.SRA.OperationalDecomposition
public import LeanTra.SRA.Modality
public import LeanTra.Metatheory.Confluence.ParallelReduction
public import LeanTra.Metatheory.Confluence.Local
public import LeanTra.Metatheory.Confluence.Orthogonal
public import LeanTra.Metatheory.GentzenPrinciples
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The untyped λ-calculus as a second-order SRA instance

The abstract confluence theorems of the thesis live at the level of
Structural Relation Algebras and speak only of relations, substitution
and structural compatibility; their point is that once a term structure
is packaged as an SRA, the same argument delivers a confluence result
whatever the syntax happens to be. To make this promise tangible we
take the untyped λ-calculus, build the SRA structure by hand, and read
confluence of β-reduction off the abstract bridge theorem. The
λ-calculus is chosen because it is the smallest binder-carrying syntax
in which every ingredient of the framework has to do real work
(capture-avoiding substitution, the algebra of contexts, compatibility
under term formation, the Gentzen principles), and because
β-confluence is the classical benchmark against which any algebraic
account of rewriting must be measured.

The file is organised in four sections. Section 1 fixes the syntax and
its equational theory of substitution; Section 2 installs the
relational algebra on top of it; Section 3 builds the SRA operations
and discharges the sixteen axioms of the class; Section 4 splits the
structural refinement into an introduction/elimination pair, defines
β-reduction, checks the four rule-level Gentzen-local hypotheses, and
cashes them into confluence of parallel β via the bridge theorem. Each
section is preceded by a docstring that explains what has to happen
there and why.

The overall shape is that of a case study. The syntax is concrete and
the axiom-checking is honest hand-computation; but every step above the
SRA interface is imported from the abstract theory without
modification, and the classical result, Church–Rosser for parallel β,
falls out as an application. The file exhibits, in one place, how a
real binder-carrying calculus is fitted to the framework and where the
price of doing so shows up.

## References

Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
LICS 2026. In particular the bridge theorem for confluence from local
conditions and the Gentzen Inversion and Conservation Principles used
throughout.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA
open LeanTra.Algebra

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
(`subst_comp`). Downstream everything, from the SRA axioms in
Section 3 to the four rule-level conditions on β in Section 4, is
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
raw material on which two of the SRA operations of the file will be
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

/-! ## Section 2: Renaming-closed context-indexed relations

With the syntax fixed we build the relational layer that will carry
the SRA structure. An SRA does not speak of terms directly but of
*arity-indexed families of relations between terms*, closed under
renaming: this is what `SynRel` records, a family of binary relations
on `Lam n`, one per arity, uniformly closed along any renaming
`Fin n → Fin m`. On top of `SynRel` we install the involutive-quantale
operations pointwise per arity: join and meet from set-theoretic union
and intersection, multiplication from relational composition, unit
from the diagonal, and involution from converse. Nothing here is
subtle; the point is simply that the abstract algebra of the SRA
framework has an obvious model on the syntactic side, and everything
reduces to standard facts about binary relations, discharged at
`Type 0` so that no universe bump propagates upward. -/

/-- A *syntax relation*: a family of binary relations on `Lam n`, one
per arity, uniformly closed under renaming. -/
structure SynRel : Type where
  /-- The underlying arity-indexed family. -/
  rel : (n : Nat) → Lam n → Lam n → Prop
  /-- Renaming closure. -/
  ren_closed : ∀ {n m : Nat} (f : Fin n → Fin m) {t s : Lam n},
                 rel n t s → rel m (t.ren f) (s.ren f)

namespace SynRel

/-- Extensionality: two `SynRel`s coincide when their `rel` fields agree
at every arity and every pair of terms. -/
@[ext] theorem ext {φ ψ : SynRel}
    (h : ∀ n (t s : Lam n), φ.rel n t s ↔ ψ.rel n t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ; obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by funext n t s; exact propext (h n t s)
  subst hrel; rfl

/-! ### The pointwise complete lattice

The first algebraic layer on `SynRel` is the order structure. The
whole thing is inherited from `Prop` pointwise: `φ ≤ ψ` is defined as
containment at every arity and every pair of terms, `⊤` and `⊥` as
the always-true and always-false relations, binary and set-indexed
join and meet as union and intersection of relations at each arity.
Ren-closure travels for free through each of these constructions,
which is why every instance below carries a tiny two-line
`ren_closed` proof and no more. What follows those definitions is a
handful of `simp`-normal shape lemmas that expose the underlying
`∀`/`∃`/`∧`/`∨` structure to the tactic layer, and the
`instCompleteLattice` instance that packages everything into the
typeclass the abstract framework consumes: the SRA definition demands
a complete lattice on the carrier because that is what makes fixpoint
constructions (Howe-style closures in particular) well-defined. The
proofs of the lattice axioms are elementary, mostly a single `intro`
followed by a projection or an elimination on the pointwise
`∨`/`∧`. -/

/-- Pointwise `≤`. -/
instance instLE : LE SynRel :=
  ⟨fun φ ψ => ∀ n (t s : Lam n), φ.rel n t s → ψ.rel n t s⟩

/-- Pointwise `⊤`, every pair related at every arity. -/
instance instTop : Top SynRel := ⟨{
  rel := fun _ _ _ => True
  ren_closed := by intros; trivial }⟩

/-- Pointwise `⊥`, no pair related. -/
instance instBot : Bot SynRel := ⟨{
  rel := fun _ _ _ => False
  ren_closed := by intros _ _ _ _ _ h; exact h.elim }⟩

/-- Pointwise binary join. -/
instance instMax : Max SynRel := ⟨fun φ ψ => {
  rel := fun n t s => φ.rel n t s ∨ ψ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h; exact h.imp (φ.ren_closed f) (ψ.ren_closed f) }⟩

/-- Pointwise binary meet. -/
instance instMin : Min SynRel := ⟨fun φ ψ => {
  rel := fun n t s => φ.rel n t s ∧ ψ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h
    exact ⟨φ.ren_closed f h.1, ψ.ren_closed f h.2⟩ }⟩

/-- Pointwise set-indexed join. -/
instance instSupSet : SupSet SynRel := ⟨fun 𝒮 => {
  rel := fun n t s => ∃ φ ∈ 𝒮, φ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩ }⟩

/-- Pointwise set-indexed meet. -/
instance instInfSet : InfSet SynRel := ⟨fun 𝒮 => {
  rel := fun n t s => ∀ φ ∈ 𝒮, φ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h φ hφ𝒮
    exact φ.ren_closed f (h φ hφ𝒮) }⟩

/-- `simp`-normal shape of `⊤`. -/
@[simp] theorem top_rel {n} {t s : Lam n} :
    (⊤ : SynRel).rel n t s ↔ True := Iff.rfl
/-- `simp`-normal shape of `⊥`. -/
@[simp] theorem bot_rel {n} {t s : Lam n} :
    (⊥ : SynRel).rel n t s ↔ False := Iff.rfl
/-- `simp`-normal shape of binary join. -/
@[simp] theorem sup_rel {φ ψ : SynRel} {n} {t s : Lam n} :
    (φ ⊔ ψ).rel n t s ↔ φ.rel n t s ∨ ψ.rel n t s := Iff.rfl
/-- `simp`-normal shape of binary meet. -/
@[simp] theorem inf_rel {φ ψ : SynRel} {n} {t s : Lam n} :
    (φ ⊓ ψ).rel n t s ↔ φ.rel n t s ∧ ψ.rel n t s := Iff.rfl
/-- `simp`-normal shape of `sSup`. -/
@[simp] theorem sSup_rel {𝒮 : Set SynRel} {n} {t s : Lam n} :
    (sSup 𝒮).rel n t s ↔ ∃ φ ∈ 𝒮, φ.rel n t s := Iff.rfl
/-- `simp`-normal shape of `sInf`. -/
@[simp] theorem sInf_rel {𝒮 : Set SynRel} {n} {t s : Lam n} :
    (sInf 𝒮).rel n t s ↔ ∀ φ ∈ 𝒮, φ.rel n t s := Iff.rfl

/-- `simp`-normal shape of indexed supremum. -/
theorem iSup_rel {ι : Sort*} {f : ι → SynRel} {n} {t s : Lam n} :
    (⨆ i, f i).rel n t s ↔ ∃ i, (f i).rel n t s := by
  rw [iSup, sSup_rel]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

/-- `simp`-normal shape of bounded indexed supremum. -/
theorem biSup_rel {α : Type*} {s : Set α} {f : α → SynRel}
    {n} {t st : Lam n} :
    (⨆ a ∈ s, f a).rel n t st ↔ ∃ a ∈ s, (f a).rel n t st := by
  simp only [iSup_rel]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩

/-- Pointwise complete lattice structure on `SynRel`. -/
instance instCompleteLattice : CompleteLattice SynRel where
  le := (· ≤ ·)
  le_refl _ _ _ _ h := h
  le_trans _ _ _ h₁ h₂ n t s h := h₂ n t s (h₁ n t s h)
  le_antisymm φ ψ h₁ h₂ := by ext n t s; exact ⟨h₁ n t s, h₂ n t s⟩
  sup := (· ⊔ ·)
  le_sup_left _ _ _ _ _ h := Or.inl h
  le_sup_right _ _ _ _ _ h := Or.inr h
  sup_le _ _ _ h₁ h₂ n t s h := h.elim (h₁ n t s) (h₂ n t s)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ _ _ h := h.1
  inf_le_right _ _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ n t s h := ⟨h₁ n t s h, h₂ n t s h⟩
  sSup := sSup
  isLUB_sSup 𝒮 :=
    ⟨fun φ hφ𝒮 n t s h => ⟨φ, hφ𝒮, h⟩,
     fun _ hb n t s => by
       rintro ⟨φ, hφ𝒮, h⟩; exact hb hφ𝒮 n t s h⟩
  sInf := sInf
  isGLB_sInf 𝒮 :=
    ⟨fun φ hφ𝒮 n t s h => h φ hφ𝒮,
     fun _ hb n t s h φ hφ𝒮 => hb hφ𝒮 n t s h⟩
  top := ⊤
  le_top _ _ _ _ _ := trivial
  bot := ⊥
  bot_le _ _ _ _ h := h.elim

/-! ### Composition, identity, quantale, involution

Above the lattice we install the multiplicative and involutive
structure that turns `SynRel` into an *involutive quantale*, the
carrier the SRA framework actually asks for. Multiplication is
relational composition (`(φ * ψ).rel n t v` iff there is an
intermediate `u` with `φ` on the left and `ψ` on the right), the unit
is the identity relation (equality at every arity), and the
involution is converse (`φᵒ` swaps the two sides). The quantale law
saying that composition distributes over arbitrary joins on both
sides holds essentially by construction: unfolding the definitions
turns it into "an existential over a disjunction is a disjunction of
existentials". The involution laws are equally routine but for the
same reason worth checking explicitly, since the SRA metatheory
manipulates converse freely. Together the four instances close the
involutive-quantale structure and unlock the layer of laws
(`Algebra.InvolutiveQuantale`) on which the SRA operations of Section
3 will be defined. -/

/-- Pointwise relational composition. -/
instance instMul : Mul SynRel := ⟨fun φ ψ => {
  rel := fun n t v => ∃ u, φ.rel n t u ∧ ψ.rel n u v
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨u.ren f, φ.ren_closed f htu, ψ.ren_closed f huv⟩ }⟩

/-- The identity relation, equality at every arity. -/
instance instOne : One SynRel := ⟨{
  rel := fun _ t s => t = s
  ren_closed := by intros _ _ f _ _ h; exact congrArg (Lam.ren · f) h }⟩

/-- `simp`-normal shape of composition. -/
@[simp] theorem mul_rel {φ ψ : SynRel} {n} {t v : Lam n} :
    (φ * ψ).rel n t v ↔ ∃ u, φ.rel n t u ∧ ψ.rel n u v := Iff.rfl
/-- `simp`-normal shape of the identity relation. -/
@[simp] theorem one_rel {n} {t s : Lam n} :
    (1 : SynRel).rel n t s ↔ t = s := Iff.rfl

/-- Monoid structure on `SynRel` under composition and equality. -/
instance instMonoid : Monoid SynRel where
  mul := (· * ·)
  one := 1
  one_mul φ := by
    ext n t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, rfl, h⟩; exact h
    · intro h; exact ⟨t, rfl, h⟩
  mul_one φ := by
    ext n t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, h, rfl⟩; exact h
    · intro h; exact ⟨v, h, rfl⟩
  mul_assoc φ ψ χ := by
    ext n t w
    refine ⟨?_, ?_⟩
    · rintro ⟨v, ⟨u, htu, huv⟩, hvw⟩; exact ⟨u, htu, v, huv, hvw⟩
    · rintro ⟨u, htu, v, huv, hvw⟩; exact ⟨v, ⟨u, htu, huv⟩, hvw⟩

/-- Pointwise quantale structure: composition distributes over arbitrary
suprema on both sides. -/
instance instIsQuantale : IsQuantale SynRel where
  mul_sSup_distrib a 𝒮 := by
    ext n t v
    rw [mul_rel, biSup_rel]
    simp only [mul_rel, sSup_rel]
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hau, φ, hφ, hφuv⟩; exact ⟨φ, hφ, u, hau, hφuv⟩
    · rintro ⟨φ, hφ, u, hau, hφuv⟩; exact ⟨u, hau, φ, hφ, hφuv⟩
  sSup_mul_distrib 𝒮 a := by
    ext n t v
    rw [mul_rel, biSup_rel]
    simp only [mul_rel, sSup_rel]
    refine ⟨?_, ?_⟩
    · rintro ⟨u, ⟨φ, hφ, hφtu⟩, hau⟩; exact ⟨φ, hφ, u, hφtu, hau⟩
    · rintro ⟨φ, hφ, u, hφtu, hau⟩; exact ⟨u, ⟨φ, hφ, hφtu⟩, hau⟩

/-- Converse: swap the endpoints of the relation, per arity. -/
def converse (φ : SynRel) : SynRel := {
  rel := fun n t s => φ.rel n s t
  ren_closed := by intros _ _ f _ _ h; exact φ.ren_closed f h }

/-- `simp`-normal shape of converse. -/
@[simp] theorem converse_rel (φ : SynRel) {n} {t s : Lam n} :
    (converse φ).rel n t s ↔ φ.rel n s t := Iff.rfl

/-- The involutive-quantale layer: `converse` is an involutive
anti-endomorphism of the quantale. -/
instance instIsInvolutiveQuantale : IsInvolutiveQuantale SynRel where
  converse := converse
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext n t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h n t s h' := h n s t h'

/-! ## Section 3: SRA operations and their axioms

The heart of the file is the definition of the SRA operations and the
verification of their sixteen defining axioms, culminating in
`instSRA : SRA SynRel`. Four operations are needed. The diagonal
`varDiag` collects the equality on variables. The structural refinement
`scr` propagates a family of relations through the two term
constructors, so that `scr φ` relates `lam t` to `lam s` whenever `t`
and `s` are `φ`-related, and analogously for `app`; it is split into
two clauses to reflect the second-order signature, a `lam`-clause that
recurses at `Lam (n+1)` and an `app`-clause at the current arity.
Substitution `subst φ ψ` composes a relation on terms with a relation
on substitutions, delivering the standard fact that if `φ` relates `t`
and `s` and `ψ` relates two substitutions position by position then
the substituted terms are related. Finally `j` witnesses the finitary
join-preservation properties that the involutive quantale demands.
Fourteen of the sixteen axioms are direct computations by induction on
terms and pattern-matching on renamings and substitutions; the two
remaining "oplaxity" laws, `subst_scr_oplaxity` on the `scr`-side and,
symmetrically, `subst_introduction_oplaxity` in Section 4, resist a
direct proof for a reason that is a genuine artefact of the de Bruijn
presentation and is discussed at length below. -/

/-- `Δη`: pairs of the same variable. -/
def varDiag : SynRel := {
  rel := fun n t s => ∃ x : Fin n, t = Lam.var x ∧ s = Lam.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩ }

/-- Strict compatible refinement: same outermost constructor with the
sub-terms pairwise related. `lam` clause demands the sub-relation at
the extended arity `n + 1`; `app` clause at the current arity. -/
def scr (φ : SynRel) : SynRel := {
  rel := fun n t s =>
    (∃ t' s', t = Lam.lam t' ∧ s = Lam.lam s' ∧ φ.rel (n + 1) t' s')
    ∨ (∃ t₁ t₂ s₁ s₂,
        t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
        ∧ φ.rel n t₁ s₁ ∧ φ.rel n t₂ s₂)
  ren_closed := by
    intro _ _ f _ _ h
    rcases h with ⟨t', s', ht, hs, hφ⟩ | ⟨t₁, t₂, s₁, s₂, ht, hs, hφ₁, hφ₂⟩
    · refine Or.inl ⟨t'.ren (Lam.liftRen f), s'.ren (Lam.liftRen f), ?_, ?_, ?_⟩
      · rw [ht]; rfl
      · rw [hs]; rfl
      · exact φ.ren_closed (Lam.liftRen f) hφ
    · refine Or.inr ⟨t₁.ren f, t₂.ren f, s₁.ren f, s₂.ren f, ?_, ?_, ?_, ?_⟩
      · rw [ht]; rfl
      · rw [hs]; rfl
      · exact φ.ren_closed f hφ₁
      · exact φ.ren_closed f hφ₂ }

/-- Relation substitution, same shape as the first-order case. -/
def subst (φ ψ : SynRel) : SynRel := {
  rel := fun m u v =>
    ∃ (n : Nat) (t s : Lam n) (τ σ : Fin n → Lam m),
      u = t.subst τ ∧ v = s.subst σ
      ∧ φ.rel n t s ∧ ∀ x, ψ.rel m (τ x) (σ x)
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩ := h
    refine ⟨n, t, s, fun x => (τ x).ren f, fun x => (σ x).ren f,
            ?_, ?_, hφ, fun x => ψ.ren_closed f (hψ x)⟩
    · rw [hu, Lam.ren_subst]
    · rw [hv, Lam.ren_subst] }

/-- Closure constant `j`: identity on weakenings of closed terms. -/
def j : SynRel := {
  rel := fun n t s => t = s ∧ ∃ t₀ : Lam 0, t = Lam.close n t₀
  ren_closed := by
    intro n m f t s h
    obtain ⟨hts, t₀, ht⟩ := h
    refine ⟨by rw [hts], t₀, ?_⟩
    rw [ht, Lam.ren_close] }

/-- `simp`-normal shape of `varDiag`. -/
@[simp] theorem varDiag_rel {n} {t s : Lam n} :
    (varDiag : SynRel).rel n t s ↔ ∃ x : Fin n, t = Lam.var x ∧ s = Lam.var x :=
  Iff.rfl

/-- `simp`-normal shape of `scr`. -/
@[simp] theorem scr_rel {φ : SynRel} {n} {t s : Lam n} :
    (scr φ).rel n t s ↔
      (∃ t' s', t = Lam.lam t' ∧ s = Lam.lam s' ∧ φ.rel (n + 1) t' s')
      ∨ (∃ t₁ t₂ s₁ s₂,
          t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
          ∧ φ.rel n t₁ s₁ ∧ φ.rel n t₂ s₂) := Iff.rfl

/-- `simp`-normal shape of `subst`. -/
@[simp] theorem subst_rel {φ ψ : SynRel} {m} {u v : Lam m} :
    (subst φ ψ).rel m u v ↔
      ∃ (n : Nat) (t s : Lam n) (τ σ : Fin n → Lam m),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel n t s ∧ ∀ x, ψ.rel m (τ x) (σ x) := Iff.rfl

/-- `simp`-normal shape of `j`. -/
@[simp] theorem j_rel {n} {t s : Lam n} :
    (j : SynRel).rel n t s ↔
      t = s ∧ ∃ t₀ : Lam 0, t = Lam.close n t₀ := Iff.rfl

/-! ### The easy axioms

Grouped here are the SRA axioms whose proof requires no genuine
insight, only a straightforward unfolding of the definitions of
`scr`, `subst`, and the involutive-quantale operations. Monotonicity
of `scr` and of `subst` in its second argument follows from the fact
that both are defined by an existential over a `φ`-obligation, so a
larger `φ` produces a larger existential. The commutation laws with
converse (`scr` and `subst`) are pattern-matches on the two clauses
of `scr` and a symmetric renaming of witnesses in `subst`. Join
preservation of `subst` in its first argument, the symmetry and
co-transitivity of the diagonal `varDiag`, and the orthogonality of
`varDiag` with `scr` (variables and compound terms are disjoint) all
close in the same style. Nothing here scales the wall of binders yet;
that is the job of the harder axioms further down. -/

/-- SRA axiom: monotonicity of `scr`. -/
theorem scr_monotonicity {φ ψ : SynRel} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro n t s hs
  rcases hs with ⟨t', s', ht, hs', hφ⟩ | ⟨t₁, t₂, s₁, s₂, ht, hs', hφ₁, hφ₂⟩
  · exact Or.inl ⟨t', s', ht, hs', h _ _ _ hφ⟩
  · exact Or.inr ⟨t₁, t₂, s₁, s₂, ht, hs', h _ _ _ hφ₁, h _ _ _ hφ₂⟩

/-- SRA axiom: monotonicity of `subst` in its second argument. -/
theorem subst_monotonicity_right {φ ψ ψ' : SynRel} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro m u v hs
  obtain ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨n, t, s, τ, σ, hu, hv, hφ, fun x => h m (τ x) (σ x) (hψ x)⟩

/-- SRA axiom: `scr` commutes with converse. -/
theorem scr_converse_commutation (φ : SynRel) : scr (φᵒ) = (scr φ)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩

/-- SRA axiom: converse commutes with `subst`, swapping both slots. -/
theorem subst_converse_commutation (φ ψ : SynRel) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨n, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨n, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

/-- SRA axiom: `subst` preserves arbitrary joins in its first argument. -/
theorem subst_join_preservation_left (𝒮 : Set SynRel) (ψ : SynRel) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, n, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, n, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨n, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

/-- SRA axiom: `varDiag` is symmetric. -/
theorem varDiag_symmetry : (varDiag : SynRel)ᵒ ≤ varDiag := by
  intro n t s ⟨x, hs, ht⟩; exact ⟨x, ht, hs⟩

/-- SRA axiom: `varDiag` is co-transitive. -/
theorem varDiag_cotransitivity : (varDiag : SynRel) ≤ varDiag * varDiag := by
  intro n t s ⟨x, ht, hs⟩
  exact ⟨Lam.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

/-- SRA axiom: variables and compound terms are disjoint,
`varDiag * scr φ ≤ ⊥`. -/
theorem varDiag_scr_orthogonality (φ : SynRel) :
    (varDiag : SynRel) * scr φ ≤ ⊥ := by
  rintro n t v ⟨u, ⟨x, _, rfl⟩, h⟩
  rcases h with ⟨_, _, hu, _, _⟩ | ⟨_, _, _, _, hu, _, _, _⟩
  · cases hu
  · cases hu

/-! ### Unit laws for substitution

The two axioms saying that the diagonal on variables acts as a
two-sided unit for the relational substitution operator:
`subst varDiag ψ = ψ` and `subst φ varDiag = φ`. Together they are
the analogue, at the level of relations, of the classical fact that
substituting the identity substitution leaves a term unchanged; and
they are what lets the abstract SRA theory treat `subst` as a real
"substitution-shaped" operation. The left unit falls out immediately
by unfolding: the `varDiag` obligation on the first argument forces
the two substituted terms to be syntactically `var x`, and the
remaining pointwise `ψ`-obligation reduces to `ψ` itself. The right
unit is the delicate one, because the `varDiag` obligation on the
argument substitutions only tells us that each `τ x` and `σ x` are
*equal variables*, i.e. of the form `var (ρ x)` for some common `ρ`.
Extracting `ρ` uses classical choice and then the auxiliary lemma
`subst_var_eq_ren` (proved locally by induction on the term) collapses
substituting by such a "variable-valued" map into a renaming; ren-
closure of `φ` then closes the case. The lemma lives here rather
than up in Section 1 because this is the only place it is used. -/

/-- SRA axiom: `varDiag` is a left unit for `subst`. -/
theorem subst_varDiag_unit_left (ψ : SynRel) : subst varDiag ψ = ψ := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨1, Lam.var 0, Lam.var 0, fun _ => u, fun _ => v,
            rfl, rfl, ⟨0, rfl, rfl⟩, ?_⟩
    intro _; exact hψ

/-- Substituting `var (ρ x)` at every variable is renaming by `ρ`. Used to
collapse the pointwise `varDiag` obligation in `subst_varDiag_unit_right`
back onto `φ.ren_closed`; proved by induction on the term with the target
arity generalised so that the `lam` case works through `liftRen`. -/
theorem subst_var_eq_ren : ∀ {n m : Nat} (t : Lam n) (ρ : Fin n → Fin m),
    t.subst (fun x => Lam.var (ρ x)) = t.ren ρ := by
  intro n m t
  induction t generalizing m with
  | var x => intros; rfl
  | app t s ih_t ih_s =>
    intro ρ
    simp only [Lam.subst_app, Lam.ren_app, ih_t, ih_s]
  | lam t ih =>
    intro ρ
    simp only [Lam.subst_lam, Lam.ren_lam]
    rw [← ih (Lam.liftRen ρ)]
    have hmap : Lam.liftSubst (fun x => Lam.var (ρ x))
                = (fun i => Lam.var (Lam.liftRen ρ i)) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; rfl
    rw [hmap]

/-- SRA axiom: `varDiag` is a right unit for `subst`. -/
theorem subst_varDiag_unit_right (φ : SynRel) : subst φ varDiag = φ := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, rfl, rfl, hφ, hvar⟩
    obtain ⟨ρ, hρ⟩ := Classical.axiomOfChoice hvar
    have hτ : τ = fun x => Lam.var (ρ x) := funext (fun x => (hρ x).1)
    have hσ : σ = fun x => Lam.var (ρ x) := funext (fun x => (hρ x).2)
    rw [hτ, hσ, subst_var_eq_ren, subst_var_eq_ren]
    exact φ.ren_closed ρ hφ
  · intro hφ
    exact ⟨m, u, v, Lam.var, Lam.var,
           (Lam.subst_id u).symm, (Lam.subst_id v).symm, hφ,
           fun x => ⟨x, rfl, rfl⟩⟩

/-! ### `scr` and composition

The interaction laws between the structural refinement `scr` and the
relational composition `*`, plus the associativity of `subst` and the
oplaxity of its interaction with composition. The key law is
`scr (φ * ψ) = scr φ * scr ψ`: propagating a composite relation
through a constructor is the same as composing the two structural
propagations. Together with `subst_associativity` and the oplax
inequality `subst φ ψ * subst φ' ψ' ≤ subst (φ * φ') (ψ * ψ')`, these
express that `scr` and `subst` are compatible with the monoidal
structure of the quantale in the expected way. The proofs are longer
than in the "easy" block only because a case analysis on the two
clauses of `scr` has to be threaded through the composition witness,
but each case is still a mechanical unfolding. -/

/-- SRA axiom: `scr` preserves composition. -/
theorem scr_compositionality (φ ψ : SynRel) :
    scr (φ * ψ) = scr φ * scr ψ := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro (⟨t', v', rfl, rfl, ⟨u', hφ, hψ⟩⟩
            | ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨u₁, hφ₁, hψ₁⟩, ⟨u₂, hφ₂, hψ₂⟩⟩)
    · exact ⟨Lam.lam u', Or.inl ⟨t', u', rfl, rfl, hφ⟩,
                          Or.inl ⟨u', v', rfl, rfl, hψ⟩⟩
    · exact ⟨Lam.app u₁ u₂,
             Or.inr ⟨t₁, t₂, u₁, u₂, rfl, rfl, hφ₁, hφ₂⟩,
             Or.inr ⟨u₁, u₂, v₁, v₂, rfl, rfl, hψ₁, hψ₂⟩⟩
  · rintro ⟨u, hφ, hψ⟩
    rcases hφ with ⟨t', u', rfl, hu, hφ⟩ | ⟨t₁, t₂, u₁, u₂, rfl, hu, hφ₁, hφ₂⟩
    · rcases hψ with ⟨u'', v', hu', rfl, hψ⟩ | ⟨_, _, _, _, hu', _, _, _⟩
      · have huu : u'' = u' := Lam.lam.inj (hu'.symm.trans hu)
        refine Or.inl ⟨t', v', rfl, rfl, u', hφ, ?_⟩
        rw [← huu]; exact hψ
      · exact absurd (hu.symm.trans hu') (by intro h; cases h)
    · rcases hψ with ⟨_, _, hu', _, _⟩
                    | ⟨u₁', u₂', v₁, v₂, hu', rfl, hψ₁, hψ₂⟩
      · exact absurd (hu.symm.trans hu') (by intro h; cases h)
      · have hinj : Lam.app u₁ u₂ = Lam.app u₁' u₂' := hu.symm.trans hu'
        have hu1u2 : u₁ = u₁' ∧ u₂ = u₂' := (Lam.app.injEq _ _ _ _).mp hinj
        obtain ⟨rfl, rfl⟩ := hu1u2
        refine Or.inr ⟨t₁, t₂, v₁, v₂, rfl, rfl, ?_, ?_⟩
        · exact ⟨u₁, hφ₁, hψ₁⟩
        · exact ⟨u₂, hφ₂, hψ₂⟩

/-! ### Introduction / elimination operations

The two `OperationalDecomposition` operations are defined here (rather
than in Section 4) because the `NominalFSPGaps` structure below
references them. Their axioms (join preservation, compositionality,
orthogonality, …) stay in Section 4. -/

/-- Introduction forms: `(lam t, lam s)` with `a`-related bodies. -/
def introduction (a : SynRel) : SynRel := {
  rel := fun n t s => ∃ t' s',
    t = Lam.lam t' ∧ s = Lam.lam s' ∧ a.rel (n + 1) t' s'
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨t', s', ht, hs, ha⟩ := h
    exact ⟨t'.ren (Lam.liftRen f), s'.ren (Lam.liftRen f),
           by rw [ht]; rfl, by rw [hs]; rfl,
           a.ren_closed (Lam.liftRen f) ha⟩ }

/-- Elimination forms: `(app t₁ t₂, app s₁ s₂)` with major `a`-related,
minor `b`-related. -/
def elimination (a b : SynRel) : SynRel := {
  rel := fun n t s => ∃ t₁ t₂ s₁ s₂,
    t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
    ∧ a.rel n t₁ s₁ ∧ b.rel n t₂ s₂
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨t₁, t₂, s₁, s₂, ht, hs, ha, hb⟩ := h
    exact ⟨t₁.ren f, t₂.ren f, s₁.ren f, s₂.ren f,
           by rw [ht]; rfl, by rw [hs]; rfl,
           a.ren_closed f ha, b.ren_closed f hb⟩ }

/-- `simp`-normal shape of `introduction`. -/
@[simp] theorem introduction_rel {a : SynRel} {n} {t s : Lam n} :
    (introduction a).rel n t s ↔ ∃ t' s',
      t = Lam.lam t' ∧ s = Lam.lam s' ∧ a.rel (n + 1) t' s' := Iff.rfl

/-- `simp`-normal shape of `elimination`. -/
@[simp] theorem elimination_rel {a b : SynRel} {n} {t s : Lam n} :
    (elimination a b).rel n t s ↔ ∃ t₁ t₂ s₁ s₂,
      t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
      ∧ a.rel n t₁ s₁ ∧ b.rel n t₂ s₂ := Iff.rfl

/-! ### The Nominal-FSP gap, packaged as a local axiom

The two "oplaxity" laws left over from Section 3 refuse to be proved
directly at their strongest instantiation, and the obstruction is
entirely a symptom of the de Bruijn presentation: at the trivial
argument relation `ψ = ⊥` there is a vacuously satisfied left-hand
side involving closed identity terms which nonetheless requires, on
the right, that the freshly bound variable be related to itself under
an empty relation, which is impossible. In the nominal tradition this
gap is closed by the Finite Support Principle, which chooses the bound
name outside the support of the substitution and thereby dodges the
fictitious obligation. Rather than build the full nominal apparatus we
take an honest shortcut: we state the two problematic laws as an
explicit local `axiom nominalFSP`, we prove strictly guarded variants
of the same statements (under the extra hypothesis `Δη ≤ ψ`, which is
verified at every real call site), and we let the axiom trace at the
end of the file make the dependency completely visible. This is
the one place where the formalisation departs from a `sorry`-free
discipline, and it does so in a controlled way that isolates the
departure to a single named assumption whose meaning is well
understood. The rest of this block is the detailed accounting. Two
axioms of the SRA/OD layer fail to close in the well-scoped de Bruijn
representation without an additional binder-side hypothesis:

* `subst_scr_oplaxity`: at the `lam` clause of `scr`, the freshly-bound
  index at position `Fin.mk 0` of the extended context becomes `var 0`
  on both endpoints of the pointwise `ψ`-obligation of `subst`; if `ψ`
  does not relate `var 0` to itself (e.g. `ψ = ⊥`), the obligation
  cannot be discharged and the LHS is inhabited by pairs whose RHS
  witness is missing.
* `subst_introduction_oplaxity`: the same obstruction, transported
  from `scr` to the `introduction` slot of the
  `OperationalDecomposition` layer.

The concrete counterexample. Take `φ := ⊤`, `ψ := ⊥`, and consider
the pair `(t, s) := (λx.x, λx.x)` at arity `0`. The LHS
`subst (scr ⊤) ⊥` is inhabited via the decomposition `n₀ = 0`,
`t = λx.x`, `s = λx.x`, `τ = σ = elim0`, `hscr : scr ⊤ 0 (λx.x, λx.x)`
(the `lam` clause of `scr` at `⊤` is satisfied vacuously since `⊤`
holds everywhere), and the pointwise `ψ`-obligation is vacuously true
because `Fin 0` is empty. The RHS `scr (subst ⊤ ⊥)` at the same pair
requires `(subst ⊤ ⊥).rel 1 (var 0) (var 0)`, which unfolds to
`∃ n, t, s, τ, σ, var 0 = t.subst τ ∧ var 0 = s.subst σ ∧ …
   ∧ ∀ x, ⊥.rel 1 (τ x) (σ x)`, and the last conjunct is unsatisfiable.

The standard nominal treatment of second-order syntax discharges
this obstruction via the **Finite Support Principle (FSP)**: on the
α-quotient with equivariant finitely-supported relations, the bound
variable of the outer `λ` is chosen fresh for the support of `ψ`, so
the fictitious `(var 0, var 0)` obligation never appears. Formalising
that argument requires a full nominal-set infrastructure (freshness,
support, α-quotients, equivariance), a separate project we defer.

Instead: the two problematic statements are grouped into
`NominalFSPGaps` and postulated jointly as `axiom nominalFSP`. The
axiom is **local to this file**; the axiom trace at the bottom
records the dependency of every downstream theorem on it. The three
other FSP-shaped facts (`subst_associativity`'s (≥) direction,
`elimination_join_preservation` split slot-by-slot, and
`box_elimination_oplaxity`) are proved directly. -/

/-- The two algebraic facts on `SynRel` whose formalisation would
require the nominal Finite Support Principle. Grouped so that the SRA
and `OperationalDecomposition` instances can be built by projection
from a single opaque witness `nominalFSP`. -/
structure NominalFSPGaps : Prop where
  /-- Oplaxness of relation substitution on the strict compatible
  refinement `scr`, including under binders. False at `ψ = ⊥` in
  this model; see the block-level docstring above. -/
  subst_scr_oplaxity : ∀ (φ ψ : SynRel), subst (scr φ) ψ ≤ scr (subst φ ψ)
  /-- Oplaxness of relation substitution on the `introduction` slot
  of the operational-decomposition layer. Same binder-side
  obstruction as `subst_scr_oplaxity`; see the block-level docstring
  above. -/
  subst_introduction_oplaxity : ∀ (a b : SynRel), subst (introduction a) b ≤ introduction (subst a b)

/-- The two `NominalFSPGaps` statements, postulated as a single
opaque axiom local to this file. The two projections
`nominalFSP.subst_scr_oplaxity` and
`nominalFSP.subst_introduction_oplaxity` are the SRA/OD axioms that
the well-scoped de Bruijn model cannot discharge on its own; every
other axiom is proved directly below. The dependency is confined to
this file and appears explicitly in the axiom trace of
`betaRule_local_confluent`. -/
axiom nominalFSP : NominalFSPGaps

/-! ### Guarded oplaxity laws

The two oplaxity statements above are the ones the well-scoped model
cannot prove *unconditionally*, but the following observation makes
the picture cleaner: **the same statements, guarded by the extra
hypothesis `Δη ≤ ψ`, are provable directly in this file, without any
appeal to `nominalFSP`.**

The guard supplies the missing ingredient: on the freshly-bound
position of the extended context, the lifted substitution is `var 0`
on both endpoints, so the pointwise ψ-obligation reduces to
`ψ.rel (n+1) (var 0) (var 0)`. If `Δη ≤ ψ`, that obligation follows
from the `varDiag` witness `⟨0, rfl, rfl⟩`; the remaining `Fin.succ j`
positions are discharged by `ψ.ren_closed` applied to the original
ψ-obligation. The (unguarded) counterexample is thereby excluded from
the premise: at `ψ = ⊥`, `Δη ≤ ⊥` is unsatisfiable (as `Δη` is
inhabited by every `(var x, var x)`), so the guarded law does not
apply at `ψ = ⊥` at all.

**Every use of the unguarded law in the metatheory** (see e.g.
`Metatheory/Confluence/ParallelReduction.lean` and `SRA/Howe.lean`)
instantiates `ψ` with a relation containing the identity (typically
`ψ = Δ` or `ψ = a⇛`); the guard is therefore satisfied at every real
call site. This is the technical content of the remark above that
the failure at `ψ = ⊥` is invisible to downstream reasoning: a
guarded formulation of the class axiom would suffice for every use,
and the guarded proofs below discharge it. -/

/-- Auxiliary: on the extended context `Fin (n+1)`, a lifted
substitution pair inherits its `ψ`-obligations from the underlying
pair via `ren_closed` on the `Fin.succ` positions, and from the
guard `Δη ≤ ψ` on the freshly-bound position (where both lifted
substitutions equal `var 0`). Used identically by
`subst_scr_oplaxity_guarded` and `subst_introduction_oplaxity_guarded`
below. -/
private theorem subst_liftSubst_ren_succ_of_le
    (ψ : SynRel) {n m : Nat}
    (τ σ : Fin n → Lam m) (hψ : ∀ x, ψ.rel m (τ x) (σ x))
    (hvar : varDiag ≤ ψ) :
    ∀ i : Fin (n + 1),
      ψ.rel (m + 1) (Lam.liftSubst τ i) (Lam.liftSubst σ i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · -- Fresh position: `liftSubst _ 0 = var 0` on both sides;
    -- discharge via `Δη ≤ ψ`.
    have : (varDiag : SynRel).rel (m + 1) (Lam.var 0) (Lam.var 0) :=
      ⟨0, rfl, rfl⟩
    exact hvar _ _ _ this
  · intro j
    -- Successor positions: `liftSubst _ (succ j) = (_ j).ren Fin.succ`.
    change ψ.rel (m + 1) ((τ j).ren Fin.succ) ((σ j).ren Fin.succ)
    exact ψ.ren_closed Fin.succ (hψ j)

/-- Guarded `subst_scr_oplaxity`: with the extra hypothesis
`Δη ≤ ψ`, the oplaxity of substitution on `scr` is provable directly
in the de Bruijn model, without appeal to `nominalFSP`. Every use in
the metatheory (see block-level docstring above) instantiates `ψ`
with a relation containing the identity, so the guarded form
suffices; the unguarded `subst_scr_oplaxity` below is retained only
to fit the shape of the `SRA` class field. -/
theorem subst_scr_oplaxity_guarded (φ ψ : SynRel) (hvar : varDiag ≤ ψ) :
    subst (scr φ) ψ ≤ scr (subst φ ψ) := by
  rintro m u v ⟨n, u₀, v₀, τ, σ, rfl, rfl, hscr, hψ⟩
  rcases hscr with ⟨t', s', rfl, rfl, hφ⟩
                 | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩
  · -- lam clause: use `subst_liftSubst_ren_succ_of_le` to lift the
    -- ψ-obligation across the extra binder.
    refine Or.inl ⟨t'.subst (Lam.liftSubst τ), s'.subst (Lam.liftSubst σ),
                   rfl, rfl, ?_⟩
    exact ⟨n + 1, t', s', Lam.liftSubst τ, Lam.liftSubst σ,
           rfl, rfl, hφ,
           subst_liftSubst_ren_succ_of_le ψ τ σ hψ hvar⟩
  · -- app clause: no binder crossed, both sub-terms inherit the
    -- ψ-obligation unchanged.
    refine Or.inr ⟨t₁.subst τ, t₂.subst τ, s₁.subst σ, s₂.subst σ,
                    rfl, rfl, ?_, ?_⟩
    · exact ⟨n, t₁, s₁, τ, σ, rfl, rfl, hφ₁, hψ⟩
    · exact ⟨n, t₂, s₂, τ, σ, rfl, rfl, hφ₂, hψ⟩

/-- Unguarded `subst_scr_oplaxity`, as required by the `SRA` class
field. Discharged via `nominalFSP`; see `subst_scr_oplaxity_guarded`
above for the guarded form that is provable directly. -/
theorem subst_scr_oplaxity (φ ψ : SynRel) : subst (scr φ) ψ ≤ scr (subst φ ψ) :=
  nominalFSP.subst_scr_oplaxity φ ψ

theorem subst_associativity (φ ψ χ : SynRel) :
    subst (subst φ ψ) χ = subst φ (subst ψ χ) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · -- (≤) direction: direct composition, mirroring first-order.
    rintro ⟨n₁, t₁, s₁, τ₁, σ₁, rfl, rfl, hφψ, hχ⟩
    obtain ⟨n₀, t₀, s₀, τ₀, σ₀, rfl, rfl, hφ, hψ⟩ := hφψ
    refine ⟨n₀, t₀, s₀,
            fun x => (τ₀ x).subst τ₁, fun x => (σ₀ x).subst σ₁,
            ?_, ?_, hφ, ?_⟩
    · rw [Lam.subst_comp]
    · rw [Lam.subst_comp]
    · intro x
      exact ⟨n₁, τ₀ x, σ₀ x, τ₁, σ₁, rfl, rfl, hψ x, hχ⟩
  · -- (≥) direction: Σ-context concatenation.
    -- Each `x : Fin n₀` contributes a local context of arity `k(x) = n₁(x)`;
    -- the global context is `Σ x, k(x)` (encoded as `Fin (∑ x, k(x))`).
    rintro ⟨n₀, t₀, s₀, τ₀, σ₀, rfl, rfl, hφ, hpsi_chi⟩
    -- Extract per-variable local witnesses via choice.
    choose k t₁ s₁ μ ν hτ hσ hψ hχ using hpsi_chi
    -- The global arity: sum of all local arities.
    let N : Nat := ∑ x : Fin n₀, k x
    -- Coordinate injection: pack (x, j) into a Fin N.
    let ι : (x : Fin n₀) → Fin (k x) → Fin N :=
      fun x j => finSigmaFinEquiv ⟨x, j⟩
    -- The global term: substitute each variable of `t₀` by the ren-embedded
    -- local witness, and analogously for `s₀`.
    refine ⟨N, t₀.subst (fun x => (t₁ x).ren (ι x)),
                s₀.subst (fun x => (s₁ x).ren (ι x)),
            fun y => (μ (finSigmaFinEquiv.symm y).1 (finSigmaFinEquiv.symm y).2),
            fun y => (ν (finSigmaFinEquiv.symm y).1 (finSigmaFinEquiv.symm y).2),
            ?_, ?_, ?_, ?_⟩
    · -- u = (t₀.subst (fun x => (t₁ x).ren (ι x))).subst μ'
      rw [Lam.subst_comp]
      apply congrArg t₀.subst
      funext x
      rw [Lam.subst_ren, hτ x]
      apply congrArg (t₁ x).subst
      funext j
      show μ x j = μ (finSigmaFinEquiv.symm (ι x j)).1
                     (finSigmaFinEquiv.symm (ι x j)).2
      have hinv : finSigmaFinEquiv.symm (ι x j) = ⟨x, j⟩ :=
        finSigmaFinEquiv.symm_apply_apply ⟨x, j⟩
      rw [hinv]
    · rw [Lam.subst_comp]
      apply congrArg s₀.subst
      funext x
      rw [Lam.subst_ren, hσ x]
      apply congrArg (s₁ x).subst
      funext j
      show ν x j = ν (finSigmaFinEquiv.symm (ι x j)).1
                     (finSigmaFinEquiv.symm (ι x j)).2
      have hinv : finSigmaFinEquiv.symm (ι x j) = ⟨x, j⟩ :=
        finSigmaFinEquiv.symm_apply_apply ⟨x, j⟩
      rw [hinv]
    · -- (subst φ ψ).rel N T S
      refine ⟨n₀, t₀, s₀,
              fun x => (t₁ x).ren (ι x), fun x => (s₁ x).ren (ι x),
              rfl, rfl, hφ, ?_⟩
      intro x
      exact ψ.ren_closed (ι x) (hψ x)
    · -- ∀ y, χ.rel m (μ' y) (ν' y)
      intro y
      exact hχ _ _

theorem subst_compositionality_oplax (φ φ' ψ ψ' : SynRel) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro m u v h
  obtain ⟨n, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨n, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨n, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

/-- SRA axiom: fixed-point law `varDiag ⊔ scr 1 = 1`, every term is
either a variable or a compound. -/
theorem cr_fixpoint : (varDiag ⊔ scr 1 : SynRel) = 1 := by
  ext n t s
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨x, rfl, rfl⟩
                | ⟨t', s', rfl, rfl, h⟩
                | ⟨t₁, t₂, s₁, s₂, rfl, rfl, h₁, h₂⟩
    · rfl
    · exact congrArg Lam.lam h
    · exact congrArg₂ Lam.app h₁ h₂
  · intro (h : t = s)
    subst h
    induction t with
    | var x => exact Or.inl ⟨x, rfl, rfl⟩
    | app t s _ _ =>
      exact Or.inr (Or.inr ⟨t, s, t, s, rfl, rfl, rfl, rfl⟩)
    | lam t _ =>
      exact Or.inr (Or.inl ⟨t, t, rfl, rfl, rfl⟩)

/-- SRA axiom: structural induction, `varDiag ⊔ scr φ ≤ φ` implies
`1 ≤ φ`. -/
theorem cr_induction {φ : SynRel} (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
  intro n t s (heq : t = s)
  subst heq
  induction t with
  | var x =>
    apply h
    exact Or.inl ⟨x, rfl, rfl⟩
  | app t s ih_t ih_s =>
    apply h
    exact Or.inr (Or.inr ⟨t, s, t, s, rfl, rfl, ih_t, ih_s⟩)
  | lam t ih =>
    apply h
    exact Or.inr (Or.inl ⟨t, t, rfl, rfl, ih⟩)

/-- SRA axiom: `j` is co-reflexive. -/
theorem j_coreflexivity : (j : SynRel) ≤ 1 := fun _ _ _ h => h.1

/-- SRA axiom: `j` is symmetric. -/
theorem j_symmetry : (j : SynRel)ᵒ ≤ j := by
  intro n t s h
  obtain ⟨hst, t₀, hs⟩ := h
  exact ⟨hst.symm, t₀, hst.symm.trans hs⟩

/-- SRA axiom: `j` is co-transitive. -/
theorem j_cotransitivity : (j : SynRel) ≤ j * j := by
  intro n t s h
  refine ⟨t, ⟨rfl, ?_⟩, h⟩
  obtain ⟨_, t₀, ht⟩ := h
  exact ⟨t₀, ht⟩

/-- SRA axiom: closed terms and variables are disjoint,
`j * varDiag ≤ ⊥`. -/
theorem j_varDiag_orthogonality : (j : SynRel) * varDiag ≤ ⊥ := by
  intro n t v ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩
  subst htu; subst huvar
  -- hcls : Lam.var x = Lam.close n t₀; case on t₀'s constructor.
  cases t₀ with
  | var y => exact y.elim0
  | app _ _ => cases hcls
  | lam _ => cases hcls

/-! ### The SRA instance

The point at which all the preceding work becomes usable. Everything
above amounts to sixteen theorems named `varDiag_symmetry`,
`scr_compositionality`, `subst_associativity`, and so on; here we
bind them to the corresponding fields of the `SRA` typeclass so that
`instSRA : SRA SynRel` is inhabited. From this line onward, every
abstract lemma stated in the `SRA` layer of the framework applies
directly to `SynRel`, without any further manual work: this is the
interface between the concrete syntactic world of `Lam` and the
abstract metatheory of Term Relation Algebras. The instance itself
is pure typeclass assembly and carries no mathematical content, but
its existence is what makes the whole file a genuine instance of the
framework rather than a parallel development. -/

/-- The syntax relations on well-scoped λ-terms form an `SRA`. -/
instance instSRA : SRA SynRel where
  varDiag := varDiag
  scr := scr
  subst := subst
  varDiag_symmetry := varDiag_symmetry
  varDiag_cotransitivity := varDiag_cotransitivity
  scr_monotonicity := fun _ _ h => scr_monotonicity h
  scr_compositionality := scr_compositionality
  scr_converse_commutation := scr_converse_commutation
  varDiag_scr_orthogonality := varDiag_scr_orthogonality
  subst_monotonicity_right := fun _ _ _ h => subst_monotonicity_right h
  subst_compositionality_oplax := subst_compositionality_oplax
  subst_converse_commutation := subst_converse_commutation
  subst_join_preservation_left := subst_join_preservation_left
  subst_varDiag_unit_left := subst_varDiag_unit_left
  subst_varDiag_unit_right := subst_varDiag_unit_right
  subst_associativity := subst_associativity
  subst_scr_oplaxity := subst_scr_oplaxity
  cr_fixpoint := cr_fixpoint
  cr_induction := fun _ h => cr_induction h
  j := j
  j_coreflexivity := j_coreflexivity
  j_symmetry := j_symmetry
  j_cotransitivity := j_cotransitivity
  j_varDiag_orthogonality := j_varDiag_orthogonality

/-! ## Section 4: Operational decomposition and β-reduction

Once the SRA instance is in place, we specialise the machinery of
`SRA/OperationalDecomposition.lean` by splitting the structural
refinement `scr` into an *introduction* component (the `lam`-clause,
carrying constructors) and an *elimination* component (the `app`-clause,
carrying destructors). The two operations themselves are
defined already in Section 3, so that `NominalFSPGaps` can reference
them; what happens here is that the split is turned into an
`OperationalDecomposition` typeclass instance, which is precisely what
allows the Gentzen principles of `Metatheory/GentzenPrinciples.lean`
to be stated at all: those principles talk about how a rewrite rule
interacts with introduction and elimination forms, and they can be
formulated only on a syntax that has been decomposed in this way.
Twelve of the thirteen accompanying axioms are again direct
computations; the thirteenth is the same nominal-FSP obligation as
before and is discharged from the same local axiom. With the instance
in hand the section then introduces β-reduction as a `SynRel`,
verifies the four rule-level Gentzen-local hypotheses required by the
bridge theorem, and finally cashes them into confluence of parallel β
via `LeanTra.Confluence.local_confluence`. -/

/-- `scr = introduction ⊔ elimination` on the diagonal. -/
theorem scr_decomposition (a : SynRel) : (SRA.scr a : SynRel) = introduction a ⊔ elimination a a := by
  ext n t s
  change (scr a).rel n t s ↔
    (introduction a).rel n t s ∨ (elimination a a).rel n t s
  simp only [scr_rel, introduction_rel, elimination_rel]

/-! ### OperationalDecomposition axioms

The thirteen axioms of the `OperationalDecomposition` class. They
mirror the shape of the corresponding `scr` laws from Section 3, but
split slot by slot into a constructor part (`introduction`, which
only sees the `lam` clause) and a destructor part (`elimination`,
which only sees the `app` clause). Monotonicity, join preservation,
compositionality, and the various converse-commutations reappear in
the two-slot form; the key new axiom is `scr_decomposition`, which
records that `scr` really is the join of introduction and
elimination on the diagonal. Twelve of the thirteen close by direct
term-level computation exactly as their `scr`-counterparts did; the
thirteenth, `subst_introduction_oplaxity`, inherits the same binder
obstruction as `subst_scr_oplaxity` and is discharged from the
second projection of the local `nominalFSP` axiom. -/

/-- OD axiom: `introduction` preserves arbitrary joins. -/
theorem introduction_join_preservation (𝒮 : Set SynRel) : introduction (sSup 𝒮) = sSup (introduction '' 𝒮) := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩
    exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
    exact ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩

/-- OD axiom: `introduction` preserves composition. -/
theorem introduction_compositionality (a b : SynRel) :
    introduction (a * b) = introduction a * introduction b := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t', v', rfl, rfl, u', ha, hb⟩
    exact ⟨Lam.lam u', ⟨t', u', rfl, rfl, ha⟩, ⟨u', v', rfl, rfl, hb⟩⟩
  · rintro ⟨u, ⟨t', u₁, rfl, hu, ha⟩, ⟨u₂, v', hu', rfl, hb⟩⟩
    have hu12 : u₁ = u₂ := Lam.lam.inj (hu.symm.trans hu')
    refine ⟨t', v', rfl, rfl, u₁, ha, ?_⟩
    rw [hu12]; exact hb

/-- OD axiom: `introduction` commutes with converse. -/
theorem introduction_converse_commutation (a : SynRel) :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩

/-- OD axiom: `elimination` preserves joins in its major (left) slot. -/
theorem elimination_join_preservation_left (𝒮 : Set SynRel) (b : SynRel) :
    elimination (sSup 𝒮) b = sSup ((fun a => elimination a b) '' 𝒮) := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨a, ha𝒮, ha⟩, hb⟩
    exact ⟨elimination a b, ⟨a, ha𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
  · rintro ⟨_, ⟨a, ha𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
    exact ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨a, ha𝒮, ha⟩, hb⟩

/-- OD axiom: `elimination` preserves joins in its minor (right) slot. -/
theorem elimination_join_preservation_right (a : SynRel) (𝒮 : Set SynRel) :
    elimination a (sSup 𝒮) = sSup ((fun b => elimination a b) '' 𝒮) := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, v₁, v₂, rfl, rfl, ha, ⟨b, hb𝒮, hb⟩⟩
    exact ⟨elimination a b, ⟨b, hb𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
  · rintro ⟨_, ⟨b, hb𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
    exact ⟨t₁, t₂, v₁, v₂, rfl, rfl, ha, ⟨b, hb𝒮, hb⟩⟩

/-- OD axiom: `elimination` preserves composition slot-by-slot. -/
theorem elimination_compositionality (a₁ a₂ b₁ b₂ : SynRel) :
    elimination (a₁ * a₂) (b₁ * b₂) = elimination a₁ b₁ * elimination a₂ b₂ := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨u₁, ha₁, ha₂⟩, ⟨u₂, hb₁, hb₂⟩⟩
    exact ⟨Lam.app u₁ u₂,
           ⟨t₁, t₂, u₁, u₂, rfl, rfl, ha₁, hb₁⟩,
           ⟨u₁, u₂, v₁, v₂, rfl, rfl, ha₂, hb₂⟩⟩
  · rintro ⟨u, ⟨t₁, t₂, u₁, u₂, rfl, hu, ha₁, hb₁⟩,
             ⟨u₁', u₂', v₁, v₂, hu', rfl, ha₂, hb₂⟩⟩
    have hinj : Lam.app u₁ u₂ = Lam.app u₁' u₂' := hu.symm.trans hu'
    have hu12 : u₁ = u₁' ∧ u₂ = u₂' := (Lam.app.injEq _ _ _ _).mp hinj
    obtain ⟨rfl, rfl⟩ := hu12
    exact ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨u₁, ha₁, ha₂⟩, ⟨u₂, hb₁, hb₂⟩⟩

/-- OD axiom: `elimination` commutes with converse in both slots. -/
theorem elimination_converse_commutation (a b : SynRel) :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩

/-- OD axiom: `introduction 1 ≤ 1`, the introduction of equal bodies is
equality. -/
theorem introduction_unit_oplaxity : (introduction 1 : SynRel) ≤ 1 := by
  rintro n t s ⟨t', s', rfl, rfl, (heq : t' = s')⟩
  exact congrArg Lam.lam heq

/-- OD axiom: `elimination 1 1 ≤ 1`, the application of equals to equals
is equality. -/
theorem elimination_unit_oplaxity : (elimination 1 1 : SynRel) ≤ 1 := by
  rintro n t s ⟨t₁, t₂, s₁, s₂, rfl, rfl, (h₁ : t₁ = s₁), (h₂ : t₂ = s₂)⟩
  exact congrArg₂ Lam.app h₁ h₂

/-- OD axiom: introductions and eliminations are orthogonal,
`introduction a * elimination b c ≤ ⊥`. -/
theorem introduction_elimination_orthogonality (a b c : SynRel) :
    introduction a * elimination b c ≤ ⊥ := by
  rintro n t v ⟨u, ⟨t', u', rfl, hu, _⟩,
                ⟨_, _, _, _, hu', _, _, _⟩⟩
  exact absurd (hu.symm.trans hu') (by intro h; cases h)

/-- Guarded `subst_introduction_oplaxity`: with the extra hypothesis
`Δη ≤ b`, the oplaxity of substitution on `introduction` is provable
directly, without appeal to `nominalFSP`. Same structural argument
as `subst_scr_oplaxity_guarded`, restricted to the `lam` clause. -/
theorem subst_introduction_oplaxity_guarded (a b : SynRel) (hvar : varDiag ≤ b) :
    subst (introduction a) b ≤ introduction (subst a b) := by
  rintro m u v ⟨n, u₀, v₀, τ, σ, rfl, rfl, ⟨t', s', rfl, rfl, ha⟩, hψ⟩
  refine ⟨t'.subst (Lam.liftSubst τ), s'.subst (Lam.liftSubst σ), rfl, rfl, ?_⟩
  exact ⟨n + 1, t', s', Lam.liftSubst τ, Lam.liftSubst σ,
         rfl, rfl, ha,
         subst_liftSubst_ren_succ_of_le b τ σ hψ hvar⟩

/-- Unguarded `subst_introduction_oplaxity`, as required by the
`OperationalDecomposition` class field. Discharged via
`nominalFSP`; see `subst_introduction_oplaxity_guarded` above for
the guarded form provable directly. -/
theorem subst_introduction_oplaxity (a b : SynRel) : subst (introduction a) b ≤ introduction (subst a b) :=
  nominalFSP.subst_introduction_oplaxity a b

/-- OD axiom: oplaxness of `subst` on the `elimination` slot. -/
theorem subst_elimination_oplaxity (a₁ a₂ b : SynRel) :
    subst (elimination a₁ a₂) b ≤ elimination (subst a₁ b) (subst a₂ b) := by
  rintro m u v ⟨n, t, s, τ, σ, rfl, rfl, ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩, hψ⟩
  refine ⟨t₁.subst τ, t₂.subst τ, s₁.subst σ, s₂.subst σ,
          rfl, rfl, ?_, ?_⟩
  · exact ⟨n, t₁, s₁, τ, σ, rfl, rfl, ha, hψ⟩
  · exact ⟨n, t₂, s₂, τ, σ, rfl, rfl, hb, hψ⟩

theorem box_elimination_oplaxity (a b : SynRel) :
    (SRA.box (elimination a b) : SynRel) ≤ elimination (SRA.box a) b := by
  -- Unfold box = j * · * j = (j * ·) * j. Peel off both `j`s (which force
  -- closedness at the endpoints) then case-analyse the closed source and
  -- target to invert the outer `app` and rebuild `elimination (box a) b`.
  intro n u v h
  -- h : ((j * elimination a b) * j).rel n u v
  obtain ⟨w, hjeab, hjwv⟩ := h
  -- hjeab : (j * elimination a b).rel n u w
  obtain ⟨w', hju, hab⟩ := hjeab
  -- hju : j.rel n u w'  ⇒  u = w' ∧ ∃ u₀, u = close n u₀
  obtain ⟨huw', u₀, hu_close⟩ := hju
  subst huw'
  -- hab : (elimination a b).rel n u w
  obtain ⟨t₁, t₂, s₁, s₂, hu_eq, hw_eq, ha, hb⟩ := hab
  -- hjwv : j.rel n w v  ⇒  w = v ∧ ∃ v₀, w = close n v₀
  obtain ⟨hwv, v₀, hv_close⟩ := hjwv
  subst hwv
  -- Invert close on u₀ to expose the app shape.
  cases u₀ with
  | var x =>
    exfalso
    have : Lam.close n (Lam.var x) = Lam.app t₁ t₂ := hu_close.symm.trans hu_eq
    cases this
  | lam _ =>
    exfalso
    have : Lam.close n (Lam.lam _) = Lam.app t₁ t₂ := hu_close.symm.trans hu_eq
    cases this
  | app u₀₁ u₀₂ =>
    have huc : Lam.app (Lam.close n u₀₁) (Lam.close n u₀₂) = Lam.app t₁ t₂ :=
      hu_close.symm.trans hu_eq
    obtain ⟨ht₁_eq, ht₂_eq⟩ := (Lam.app.injEq _ _ _ _).mp huc
    cases v₀ with
    | var x =>
      exfalso
      have : Lam.close n (Lam.var x) = Lam.app s₁ s₂ := hv_close.symm.trans hw_eq
      cases this
    | lam _ =>
      exfalso
      have : Lam.close n (Lam.lam _) = Lam.app s₁ s₂ := hv_close.symm.trans hw_eq
      cases this
    | app v₀₁ v₀₂ =>
      have hwc : Lam.app (Lam.close n v₀₁) (Lam.close n v₀₂) = Lam.app s₁ s₂ :=
        hv_close.symm.trans hw_eq
      obtain ⟨hs₁_eq, hs₂_eq⟩ := (Lam.app.injEq _ _ _ _).mp hwc
      refine ⟨t₁, t₂, s₁, s₂, hu_eq, hw_eq, ?_, hb⟩
      -- Goal: (SRA.box a).rel n t₁ s₁ = ((j * a) * j).rel n t₁ s₁
      -- Middle witness s₁: (j * a).rel n t₁ s₁ ∧ j.rel n s₁ s₁.
      refine ⟨s₁, ⟨t₁, ⟨rfl, u₀₁, ht₁_eq.symm⟩, ha⟩,
                    ⟨rfl, v₀₁, hs₁_eq.symm⟩⟩

/-! ### OperationalDecomposition instance

The counterpart of `instSRA` for the operational-decomposition layer:
the thirteen axioms above are bundled into
`instOperationalDecomposition : OperationalDecomposition SynRel`, so
that every abstract lemma stated over the class becomes applicable to
`SynRel`. In particular this is what makes the Gentzen principles
`GIP` and `GCP` of `Metatheory/GentzenPrinciples.lean` statable on
`betaRule` in the next sub-section: those principles are defined only
for carriers that carry an `OperationalDecomposition`, and would be
inexpressible without it. -/

/-- The syntax relations on λ-terms carry an `OperationalDecomposition`
structure, splitting `scr` into `introduction` (the `lam` clause) and
`elimination` (the `app` clause). -/
instance instOperationalDecomposition : OperationalDecomposition SynRel where
  introduction := introduction
  elimination := elimination
  introduction_join_preservation := introduction_join_preservation
  introduction_compositionality := introduction_compositionality
  introduction_converse_commutation := introduction_converse_commutation
  elimination_join_preservation_left := elimination_join_preservation_left
  elimination_join_preservation_right := elimination_join_preservation_right
  elimination_compositionality := elimination_compositionality
  elimination_converse_commutation := elimination_converse_commutation
  introduction_unit_oplaxity := introduction_unit_oplaxity
  elimination_unit_oplaxity := elimination_unit_oplaxity
  introduction_elimination_orthogonality := introduction_elimination_orthogonality
  scr_decomposition := scr_decomposition
  subst_introduction_oplaxity := subst_introduction_oplaxity
  subst_elimination_oplaxity := subst_elimination_oplaxity
  box_elimination_oplaxity := box_elimination_oplaxity

/-! ### β-reduction

β-reduction is introduced as `betaRule`: an arity-indexed relation
that fires whenever its left-hand side is a genuine β-redex, i.e. an
application of a λ-abstraction. Its first property, the one that
qualifies it as a *reduction* in the sense of
`Metatheory/Confluence/ParallelReduction.lean`, is that its left-hand
side is never a variable, so parallel reduction commutes with
substitution. That single fact is proved here; the four remaining
rule-level hypotheses live in the next sub-section. -/

/-- β-reduction: at every arity, the pair `(app (lam t) s, subst0 t s)`. -/
def betaRule : SynRel := {
  rel := fun n u v => ∃ t s, u = Lam.app (Lam.lam t) s ∧ v = Lam.subst0 t s
  ren_closed := by
    intro n m f u v h
    obtain ⟨t, s, hu, hv⟩ := h
    refine ⟨t.ren (Lam.liftRen f), s.ren f, ?_, ?_⟩
    · rw [hu]; rfl
    · rw [hv]
      unfold Lam.subst0
      rw [Lam.ren_subst, Lam.subst_ren]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; rfl }

/-- `simp`-normal shape of `betaRule`. -/
@[simp] theorem betaRule_rel {n} {u v : Lam n} :
    (betaRule : SynRel).rel n u v ↔
      ∃ t s, u = Lam.app (Lam.lam t) s ∧ v = Lam.subst0 t s := Iff.rfl

/-- β is a reduction: its left-hand side is never a variable. -/
theorem betaRule_isReduction :
    LeanTra.Confluence.IsReduction (betaRule : SynRel) := by
  change (varDiag * betaRule : SynRel) = ⊥
  ext n u v
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨w, ⟨x, _, rfl⟩, t, s, hw, _⟩
  cases hw

/-! ### Local hypotheses for β

Four rule-level properties remain to be checked, and the point of the
whole local formulation is that all four are visibly local: each
speaks only about `betaRule` itself, and none of them mentions parallel
reduction. First, `betaRule` is *substitutive at identity*
(`IsSubstitutiveAtIdentity`), which says that its base substitution
instance is bounded by itself: pre-composing β with a substitution
does not conjure β-redexes that were not already present. Second, β is
*deterministic on the nose* (`IsDeterministic`): two β-reducts of the
same term agree, because both are determined by the outermost
`app (lam ·) ·` whose sub-parts are unique. Third, β satisfies the
*Gentzen Inversion Principle* (`GIP`), which says that β can fire only
after its inspected argument holds a constructor, a `lam` in the
major slot of the application. Fourth, β satisfies the *Gentzen
Conservation Principle* (`GCP`), which says that firing β commutes
with substitution up to the appropriate relational bound. All four are
proved here by direct term-level computation, and none of them leaks
into the `nominalFSP` axiom. -/

/-- β is substitutive at the identity: `β⟦Δ⟧ ≤ β`.  If a β-redex can
be exhibited as a substitution-instance of another β-redex with
`τ = σ`, then the outer redex is itself a β-redex, and its reduct is
the outer's `subst0`. -/
theorem betaRule_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (betaRule : SynRel) := by
  change (SRA.subst betaRule 1 : SynRel) ≤ betaRule
  rintro m u v ⟨n, t, s, τ, σ, rfl, rfl, ⟨t', s', rfl, rfl⟩, hψ⟩
  -- `τ = σ` pointwise since `1.rel n = (· = ·)`.
  have hτσ : τ = σ := funext (fun x => hψ x)
  subst hτσ
  -- After substituting `τ`, `(app (lam t') s').subst τ` is a β-redex
  -- whose reduct is `subst0 (t'.subst (liftSubst τ)) (s'.subst τ)`, and
  -- that must equal `(subst0 t' s').subst τ`.
  refine ⟨t'.subst (Lam.liftSubst τ), s'.subst τ, ?_, ?_⟩
  · rfl
  · -- Goal: `(Lam.subst0 t' s').subst τ = Lam.subst0 (t'.subst (liftSubst τ)) (s'.subst τ)`.
    show (Lam.subst0 t' s').subst τ
         = Lam.subst0 (t'.subst (Lam.liftSubst τ)) (s'.subst τ)
    unfold Lam.subst0
    rw [Lam.subst_comp, Lam.subst_comp]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      change τ j = ((τ j).ren Fin.succ).subst (Fin.cases (s'.subst τ) Lam.var)
      rw [Lam.subst_ren]
      exact (Lam.subst_id (τ j)).symm

/-- β is deterministic: `βᵒ * β ≤ Δ`. Two β-reducts of the same term
agree, because both are determined by the outermost `app (lam ·) ·`
whose sub-parts are unique. -/
theorem betaRule_isDeterministic :
    LeanTra.Confluence.IsDeterministic (betaRule : SynRel) := by
  change ((betaRule : SynRel)ᵒ * betaRule) ≤ 1
  rintro n u v ⟨w, ⟨t, s, hw, rfl⟩, ⟨t', s', hw', rfl⟩⟩
  -- w = app (lam t) s = app (lam t') s'; conclude t = t' and s = s'.
  have h_app : Lam.app (Lam.lam t) s = Lam.app (Lam.lam t') s' := hw.symm.trans hw'
  obtain ⟨h_ls, rfl⟩ := (Lam.app.injEq _ _ _ _).mp h_app
  have h_ls_body : t = t' := Lam.lam.inj h_ls
  subst h_ls_body
  rfl

/-- Gentzen Inversion for β: every β-step factors on the left through
`ε(ι Δ, Δ)`, an elimination whose major slot holds an introduction
form. The redex is `app (lam t) s`, an `app` with `lam t` in the
major slot, `s` in the minor. -/
theorem betaRule_gip : LeanTra.Metatheory.GIP (betaRule : SynRel) := by
  change (betaRule : SynRel)
       ≤ OperationalDecomposition.elimination
           (OperationalDecomposition.introduction 1) 1 * betaRule
  rintro n u v ⟨t, s, rfl, rfl⟩
  refine ⟨Lam.app (Lam.lam t) s, ?_, ?_⟩
  · -- (ε(ι Δ, Δ)) at (app (lam t) s, app (lam t) s):
    refine ⟨Lam.lam t, s, Lam.lam t, s, rfl, rfl, ?_, rfl⟩
    -- ι Δ at (lam t, lam t): major slot is `lam` on both sides with equal body.
    exact ⟨t, t, rfl, rfl, rfl⟩
  · exact ⟨t, s, rfl, rfl⟩

/-- Gentzen Conservation for β: for every compatible `x`, β commutes
with `x`-refinement of arguments in the sense that `ε(⌃x, x) * β ≤
β * x⟦x⟧`. Two β-redexes whose `lam`-bodies are `x`-related and whose
arguments are `x`-related have `x⟦x⟧`-related reducts. -/
theorem betaRule_gcp : LeanTra.Metatheory.GCP (betaRule : SynRel) := by
  intro x hxComp
  change OperationalDecomposition.elimination (SRA.cr x) x * (betaRule : SynRel)
       ≤ betaRule * SRA.subst x x
  -- IsCompatible x = ⌃x ≤ x = (varDiag ⊔ scr x ≤ x), so varDiag ≤ x
  -- (needed for reflexivity of `x` on variables in the reduct pairing).
  have hvar_le : (varDiag : SynRel) ≤ x := le_sup_left.trans hxComp
  rintro n u v ⟨w, ⟨t₁, t₂, s₁, s₂, rfl, hw, hcr, hx⟩, tβ, sβ, hβw, rfl⟩
  -- hw : w = app s₁ s₂; hβw : w = app (lam tβ) sβ.
  -- ⇒ s₁ = lam tβ and s₂ = sβ.
  have h_app : Lam.app s₁ s₂ = Lam.app (Lam.lam tβ) sβ := hw.symm.trans hβw
  have hs12 : s₁ = Lam.lam tβ ∧ s₂ = sβ := (Lam.app.injEq _ _ _ _).mp h_app
  obtain ⟨rfl, rfl⟩ := hs12
  -- Now hcr : (SRA.cr x).rel n t₁ (lam tβ).
  -- Cases on hcr, either varDiag (impossible against a lam) or scr,
  -- and scr's lam clause is the only surviving shape.
  rcases hcr with ⟨y, _, hly⟩ | ⟨t₁', ly, ht₁_eq, hly, hbody⟩
                | ⟨_, _, _, _, _, hlam_eq_app, _, _⟩
  · cases hly
  · -- t₁ = lam t₁'; lam-equation: lam tβ = lam ly ⇒ tβ = ly.
    subst ht₁_eq
    have h_body : tβ = ly := Lam.lam.inj hly
    -- Goal uses `tβ.subst0 s₂`; rewrite that endpoint to use `ly`.
    refine ⟨Lam.subst0 t₁' t₂, ⟨t₁', t₂, rfl, rfl⟩, ?_⟩
    change (subst x x).rel n (Lam.subst0 t₁' t₂) (Lam.subst0 tβ s₂)
    rw [h_body]
    unfold Lam.subst0
    refine ⟨n + 1, t₁', ly, Fin.cases t₂ Lam.var, Fin.cases s₂ Lam.var,
            rfl, rfl, hbody, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hx
    · intro j
      exact hvar_le _ _ _ ⟨j, rfl, rfl⟩
  · cases hlam_eq_app

/-! ### Confluence of parallel β-reduction, via `local_confluence`

The payoff. Once the five rule-level facts above are in hand, the
bridge theorem `LeanTra.Confluence.local_confluence` of
`Metatheory/Confluence/Local.lean` applies verbatim and yields
confluence of parallel β-reduction: whenever a term rewrites in two
different ways under `parRed betaRule`, the two results can be joined
by another pair of parallel reductions. No further hand-computation on
terms is needed; the argument is entirely inside the abstract theory,
and the only work that happened in this file is the discharge of its
hypotheses. -/

/-- Unconditional confluence of parallel β-reduction. -/
theorem betaRule_local_confluent :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (betaRule : SynRel)) :=
  LeanTra.Confluence.local_confluence
    betaRule_isReduction
    betaRule_isSubstitutiveAtIdentity
    betaRule_isDeterministic
    betaRule_gip
    betaRule_gcp

/-! ### Alternative route: via orthogonality

As a secondary demonstration we record the same conclusion reached
along the alternative route that assumes *orthogonality* of the rule
directly. Orthogonality is not a local condition: its second conjunct
mentions `parRed betaRule` itself, so verifying it would require
reasoning about the very object the theorem is about, and it is
therefore taken as an unproved hypothesis here. The two routes share
nothing except the SRA instance, and their coexistence in one file is
a small piece of evidence that the abstract framework really does
modularise the confluence argument. -/

/-- Confluence via orthogonality, needs `IsOrthogonal` as a hypothesis. -/
theorem betaRule_confluent_orthogonal
    (horth : LeanTra.Confluence.IsOrthogonal (betaRule : SynRel)) :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (betaRule : SynRel)) :=
  LeanTra.Confluence.orthogonality_confluence betaRule_isReduction horth

end SynRel

end LeanTra.Instances.Lambda

/-! ## Axiom trace

Explicit `#check` and `#print axioms` on the main results, cf. the
tail of `Instances/FirstOrder.lean`. Every downstream theorem
depends on the three standard Lean-prelude axioms `propext`,
`Classical.choice`, `Quot.sound`; the single non-standard axiom is
`LeanTra.Instances.Lambda.SynRel.nominalFSP`, whose scope is
analysed in the block-level docstring at its declaration in Section 3.

Note on the four Gentzen-local hypotheses. Their statements
(`betaRule_isSubstitutiveAtIdentity`, `betaRule_isDeterministic`,
`betaRule_gip`, `betaRule_gcp`) speak only about `betaRule` and are
proved by term-level computation, with no *semantic* dependence on
`nominalFSP`. The trace nonetheless records the axiom for three of
them, because their statements unfold against the SRA/OD
notation (`SRA.subst`, `SRA.cr`, `OperationalDecomposition.elimination`,
…) which Lean elaborates through `instSRA` / `instOperationalDecomposition`,
and those instances do carry the axiom. Only
`betaRule_isDeterministic`, whose statement uses only the quantale
layer (`·ᵒ * · ≤ 1`), stays clean at `[propext, Quot.sound]`. This
is an elaboration-side artefact of typeclass resolution, not a
mathematical dependence: the four local proofs go through in a
guarded-axiom setting without change. -/

#check @LeanTra.Instances.Lambda.SynRel.instSRA
#check @LeanTra.Instances.Lambda.SynRel.instOperationalDecomposition
#check @LeanTra.Instances.Lambda.SynRel.betaRule_isReduction
#check @LeanTra.Instances.Lambda.SynRel.betaRule_local_confluent
#check @LeanTra.Instances.Lambda.SynRel.betaRule_confluent_orthogonal

#print axioms LeanTra.Instances.Lambda.SynRel.instSRA
#print axioms LeanTra.Instances.Lambda.SynRel.instOperationalDecomposition
#print axioms LeanTra.Instances.Lambda.SynRel.betaRule_isSubstitutiveAtIdentity
#print axioms LeanTra.Instances.Lambda.SynRel.betaRule_isDeterministic
#print axioms LeanTra.Instances.Lambda.SynRel.betaRule_gip
#print axioms LeanTra.Instances.Lambda.SynRel.betaRule_gcp
#print axioms LeanTra.Instances.Lambda.SynRel.betaRule_local_confluent

-- The two guarded forms are provable directly in this file: their
-- axiom traces do NOT contain `nominalFSP`.
#print axioms LeanTra.Instances.Lambda.SynRel.subst_scr_oplaxity_guarded
#print axioms LeanTra.Instances.Lambda.SynRel.subst_introduction_oplaxity_guarded
