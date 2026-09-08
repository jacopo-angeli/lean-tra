/-
Master's thesis: Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Function.Basic
public import LeanTra.Algebra.InvolutiveQuantale
public import LeanTra.SRA.Basic
public import LeanTra.SRA.Modality
public import LeanTra.SRA.OperationalDecomposition
public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Metatheory.Confluence.Local
public import LeanTra.Metatheory.Determinism.BigStep

/-!
# Peano arithmetic as a first-order term-relation algebra

The abstract bridge theorem in `Metatheory/Confluence/Local.lean` proves
that, on an involutive quantale equipped with the `SRA` and
`OperationalDecomposition` typeclasses, any element `a` satisfying five
local conditions — `IsReduction`, `IsSubstitutiveAtIdentity`,
`IsDeterministic`, Gentzen's inversion `GIP`, Gentzen's conservation
`GCP` — has a confluent parallel-reduction closure. The statement is
term-free: no notion of context, variable, or substitution appears in
it. This file grounds the abstract statement in a concrete syntax by
instantiating the whole typeclass tower on the Peano-arithmetic
signature
```
zero : ()             — nullary introduction (constructor)
succ : (0)            — unary  introduction (constructor)
plus : (0, 0)         — binary elimination  (destructor), slot 0 major
mult : (0, 0)         — binary elimination  (destructor), slot 0 major
```
and the four defining rewrite rules
```
plus(zero,   n) → n
plus(succ m, n) → succ (plus m n)
mult(zero,   n) → zero
mult(succ m, n) → plus (mult m n) n
```
and reading off confluence as an immediate corollary of the bridge
theorem.

Building this instance forces a specific sequence of constructions,
each conceptually independent but each required by the next. First we
fix the inductive type `Tm Γ` of Peano terms in a type-valued context Γ
and its Kleisli-monad structure (`subst`, `ren`). Next we build
`SynRel`, the involutive quantale of renaming-closed context-indexed
binary relations on `Tm`, which is the algebraic carrier the SRA
typeclass expects. On top of `SynRel` we define the four SRA
operations `varDiag`, `scr`, `subst`, `j` and discharge their nineteen
accompanying axioms, then package the result as `instance SRA SynRel`.
We repeat the same discipline for the intro / elim decomposition of
`scr`, defining `introduction` and `elimination` and discharging the
fourteen axioms of `OperationalDecomposition`. Only at that point do we
state the primitive reduction `rule` as a `SynRel`, verify the five
bridge-theorem hypotheses on it, and obtain confluence.

Two design decisions shape the whole file. First, a context is any
type, not a finite subset of a global name universe. Renamings and
substitutions are then plain functions, α-issues disappear at the
syntax level, but a term and any of its weakenings are formally
distinct objects transported by explicit `Tm.ren`; the visible cost is
the dependent-sum context merge in the proof of `subst_associativity`.
Second, the `OperationalDecomposition` axiom `introduction (sSup s) =
sSup (introduction '' s)` was relaxed to require `s.Nonempty`: without
this the nullary constructor `zero` would force `introduction ⊥` to
disagree with `⊥`, since `introduction φ` on `(zero, zero)` is true
regardless of `φ`. The paper only requires ω-cocontinuity of the
constructor semirelator (Def. 6, p. 11), and the internal framework
consumers of the axiom all apply it to non-empty joins, so the
relaxation is faithful to the paper and locally invisible.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.* LICS 2026
-/
@[expose] public section

set_option linter.style.show false
set_option linter.unusedTactic false

open scoped IsInvolutiveQuantale

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

/-!
With the syntactic layer in place, we now construct the algebraic
carrier on which the whole SRA machinery will live: `SynRel`, the type
of renaming-closed context-indexed binary relations on `Tm`. Concretely
an element of `SynRel` is a family of binary relations `φ.rel Γ : Tm Γ
→ Tm Γ → Prop`, one per context type Γ, together with a coherence
condition — the family is closed under renaming. The coherence
condition is the minimal amount of syntax-sensitivity the definition
needs; every operation defined on top of `SynRel` will preserve it, so
we never have to think about it explicitly again.

Pointwise from `Prop`, `SynRel` inherits a complete lattice (order is
pointwise implication, meets and joins are conjunction and disjunction),
a monoid whose product is relational composition `∃ u, φ t u ∧ ψ u v`
and whose unit is the pointwise identity `t = s`, a quantale
(composition distributes over arbitrary joins), and an involution
(converse swaps the two arguments). These four layers of structure are
exactly the algebraic content the `SRA` typeclass expects of its
carrier, so once `SynRel` carries them, the class hypotheses of every
downstream lemma will be discharged automatically.
-/

/-- A *syntax relation*: a family of binary relations on `Tm Γ`, one
per context type `Γ`, closed under renaming. -/
structure SynRel : Type 1 where
  rel : (Γ : Type) → Tm Γ → Tm Γ → Prop
  ren_closed : ∀ {Γ Δ : Type} (f : Γ → Δ) {t s : Tm Γ},
                 rel Γ t s → rel Δ (t.ren f) (s.ren f)

namespace SynRel

@[ext]
theorem ext {φ ψ : SynRel}
    (h : ∀ Γ (t s : Tm Γ), φ.rel Γ t s ↔ ψ.rel Γ t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ
  obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by funext Γ t s; exact propext (h Γ t s)
  subst hrel; rfl

/-!
The order on `SynRel` is pointwise implication, `⊤` and `⊥` are the
constantly-true and constantly-false families, meets and joins are
pointwise conjunction and disjunction, and arbitrary sups and infs
follow the same pattern using an existential (resp. universal) over
the index set. Each of these operations preserves renaming-closure by
inspection.
-/

instance instLE : LE SynRel :=
  ⟨fun φ ψ => ∀ Γ (t s : Tm Γ), φ.rel Γ t s → ψ.rel Γ t s⟩

theorem le_iff {φ ψ : SynRel} :
    φ ≤ ψ ↔ ∀ Γ (t s : Tm Γ), φ.rel Γ t s → ψ.rel Γ t s := Iff.rfl

instance instTop : Top SynRel := ⟨{
  rel := fun _ _ _ => True
  ren_closed := by intros; trivial
}⟩

instance instBot : Bot SynRel := ⟨{
  rel := fun _ _ _ => False
  ren_closed := by intros _ _ _ _ _ h; exact h.elim
}⟩

instance instMax : Max SynRel := ⟨fun φ ψ => {
  rel := fun Γ t s => φ.rel Γ t s ∨ ψ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    exact h.imp (φ.ren_closed f) (ψ.ren_closed f)
}⟩

instance instMin : Min SynRel := ⟨fun φ ψ => {
  rel := fun Γ t s => φ.rel Γ t s ∧ ψ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    exact ⟨φ.ren_closed f h.1, ψ.ren_closed f h.2⟩
}⟩

instance instSupSet : SupSet SynRel := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∃ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩
}⟩

instance instInfSet : InfSet SynRel := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∀ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h φ hφ𝒮
    exact φ.ren_closed f (h φ hφ𝒮)
}⟩

/-!
Boilerplate: the projection lemmas that unfold each lattice operation
back to its `Prop`-level content. Marked `@[simp]` so that `simp` will
push through these without the reader having to remember the exact
definition of, e.g., `sSup`.
-/

@[simp] theorem top_rel {Γ} {t s : Tm Γ} :
    (⊤ : SynRel).rel Γ t s ↔ True := Iff.rfl

@[simp] theorem bot_rel {Γ} {t s : Tm Γ} :
    (⊥ : SynRel).rel Γ t s ↔ False := Iff.rfl

@[simp] theorem sup_rel {φ ψ : SynRel} {Γ} {t s : Tm Γ} :
    (φ ⊔ ψ).rel Γ t s ↔ φ.rel Γ t s ∨ ψ.rel Γ t s := Iff.rfl

@[simp] theorem inf_rel {φ ψ : SynRel} {Γ} {t s : Tm Γ} :
    (φ ⊓ ψ).rel Γ t s ↔ φ.rel Γ t s ∧ ψ.rel Γ t s := Iff.rfl

@[simp] theorem sSup_rel {𝒮 : Set SynRel} {Γ} {t s : Tm Γ} :
    (sSup 𝒮).rel Γ t s ↔ ∃ φ ∈ 𝒮, φ.rel Γ t s := Iff.rfl

@[simp] theorem sInf_rel {𝒮 : Set SynRel} {Γ} {t s : Tm Γ} :
    (sInf 𝒮).rel Γ t s ↔ ∀ φ ∈ 𝒮, φ.rel Γ t s := Iff.rfl

theorem iSup_rel {κ : Sort*} {f : κ → SynRel} {Γ} {t s : Tm Γ} :
    (⨆ i, f i).rel Γ t s ↔ ∃ i, (f i).rel Γ t s := by
  rw [iSup, sSup_rel]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

theorem biSup_rel {α : Type*} {s : Set α} {f : α → SynRel}
    {Γ} {t st : Tm Γ} :
    (⨆ a ∈ s, f a).rel Γ t st ↔ ∃ a ∈ s, (f a).rel Γ t st := by
  simp only [iSup_rel]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, h⟩

/-!
Assembly of the pointwise operations into a `CompleteLattice SynRel`
instance. Each field is discharged by the corresponding pointwise fact
already proved.
-/

instance instCompleteLattice : CompleteLattice SynRel where
  le := (· ≤ ·)
  le_refl _ _ _ _ h := h
  le_trans _ _ _ h₁ h₂ Γ t s h := h₂ Γ t s (h₁ Γ t s h)
  le_antisymm φ ψ h₁ h₂ := by
    ext Γ t s
    exact ⟨h₁ Γ t s, h₂ Γ t s⟩
  sup := (· ⊔ ·)
  le_sup_left _ _ _ _ _ h := Or.inl h
  le_sup_right _ _ _ _ _ h := Or.inr h
  sup_le _ _ _ h₁ h₂ Γ t s h := h.elim (h₁ Γ t s) (h₂ Γ t s)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ _ _ h := h.1
  inf_le_right _ _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ Γ t s h := ⟨h₁ Γ t s h, h₂ Γ t s h⟩
  sSup := sSup
  isLUB_sSup 𝒮 :=
    ⟨fun φ hφ𝒮 Γ t s h => ⟨φ, hφ𝒮, h⟩,
     fun _ hb Γ t s => by
       rintro ⟨φ, hφ𝒮, h⟩; exact hb hφ𝒮 Γ t s h⟩
  sInf := sInf
  isGLB_sInf 𝒮 :=
    ⟨fun φ hφ𝒮 Γ t s h => h φ hφ𝒮,
     fun _ hb Γ t s h φ hφ𝒮 => hb hφ𝒮 Γ t s h⟩
  top := ⊤
  le_top _ _ _ _ _ := trivial
  bot := ⊥
  bot_le _ _ _ _ h := h.elim

/-!
Composition of relations `(φ * ψ).rel t v := ∃ u, φ t u ∧ ψ u v`, the
identity relation `1 := (fun t s => t = s)`, distributivity of `*` over
`sSup`, and converse: together these promote `SynRel` from a complete
lattice to an involutive quantale, exactly the algebraic layer the SRA
typeclass takes for granted.
-/

instance instMul : Mul SynRel := ⟨fun φ ψ => {
  rel := fun Γ t v => ∃ u, φ.rel Γ t u ∧ ψ.rel Γ u v
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨u.ren f, φ.ren_closed f htu, ψ.ren_closed f huv⟩
}⟩

instance instOne : One SynRel := ⟨{
  rel := fun _ t s => t = s
  ren_closed := by
    intros _ _ f _ _ h; exact congrArg (Tm.ren · f) h
}⟩

@[simp] theorem mul_rel {φ ψ : SynRel} {Γ} {t v : Tm Γ} :
    (φ * ψ).rel Γ t v ↔ ∃ u, φ.rel Γ t u ∧ ψ.rel Γ u v := Iff.rfl

@[simp] theorem one_rel {Γ} {t s : Tm Γ} :
    (1 : SynRel).rel Γ t s ↔ t = s := Iff.rfl

instance instMonoid : Monoid SynRel where
  mul := (· * ·)
  one := 1
  one_mul φ := by
    ext Γ t v
    constructor
    · rintro ⟨u, rfl, h⟩; exact h
    · intro h; exact ⟨t, rfl, h⟩
  mul_one φ := by
    ext Γ t v
    constructor
    · rintro ⟨u, h, rfl⟩; exact h
    · intro h; exact ⟨v, h, rfl⟩
  mul_assoc φ ψ χ := by
    ext Γ t w
    constructor
    · rintro ⟨v, ⟨u, htu, huv⟩, hvw⟩; exact ⟨u, htu, v, huv, hvw⟩
    · rintro ⟨u, htu, v, huv, hvw⟩; exact ⟨v, ⟨u, htu, huv⟩, hvw⟩

instance instIsQuantale : IsQuantale SynRel where
  mul_sSup_distrib a 𝒮 := by
    ext Γ t v
    rw [mul_rel, biSup_rel]
    simp only [mul_rel, sSup_rel]
    constructor
    · rintro ⟨u, hau, φ, hφ, hφuv⟩; exact ⟨φ, hφ, u, hau, hφuv⟩
    · rintro ⟨φ, hφ, u, hau, hφuv⟩; exact ⟨u, hau, φ, hφ, hφuv⟩
  sSup_mul_distrib 𝒮 a := by
    ext Γ t v
    rw [mul_rel, biSup_rel]
    simp only [mul_rel, sSup_rel]
    constructor
    · rintro ⟨u, ⟨φ, hφ, hφtu⟩, hau⟩; exact ⟨φ, hφ, u, hφtu, hau⟩
    · rintro ⟨φ, hφ, u, hφtu, hau⟩; exact ⟨u, ⟨φ, hφ, hφtu⟩, hau⟩

def converse (φ : SynRel) : SynRel := {
  rel := fun Γ t s => φ.rel Γ s t
  ren_closed := by
    intros _ _ f _ _ h; exact φ.ren_closed f h
}

@[simp] theorem converse_rel (φ : SynRel) {Γ} {t s : Tm Γ} :
    (converse φ).rel Γ t s ↔ φ.rel Γ s t := Iff.rfl

instance instIsInvolutiveQuantale : IsInvolutiveQuantale SynRel where
  converse := converse
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext Γ t v
    constructor
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h Γ t s h' := h Γ s t h'

/-!
A sanity check: `⊥ ≠ ⊤` on `SynRel`, hence `Nontrivial SynRel`. Without
this the SRA axioms would be vacuously satisfied by the degenerate
one-point carrier, which is not what we want.
-/

theorem bot_ne_top : (⊥ : SynRel) ≠ ⊤ := by
  intro h
  have hle : (⊤ : SynRel) ≤ ⊥ := h ▸ le_refl _
  exact hle Unit (Tm.var ()) (Tm.var ()) trivial

instance instNontrivial : Nontrivial SynRel := ⟨⊥, ⊤, bot_ne_top⟩

/-!
`SynRel` is now an involutive quantale, so we can define the four
operations the `SRA` typeclass demands and start discharging their
axioms. The four operations are `varDiag` (the variable co-equivalence,
which relates two terms iff they are the same variable), `scr` (the
strict compatible refinement, which relates two terms iff they have the
same outermost constructor with pairwise `φ`-related sub-terms), `subst`
(relation substitution, the categorical action of substitutions on
relations), and `j` (the closure constant, which relates a term to
itself provided the term is the weakening of a closed term).

Between the four operations the SRA class prescribes nineteen axioms,
which we discharge in three passes ordered by technical difficulty. The
first pass — monotonicity, commutation with converse, join-preservation
in the second slot of `subst`, symmetry and co-transitivity of `varDiag`
— is unfolding and symbol-pushing. The second pass needs some real work:
`subst_varDiag_unit_right` requires `Classical.axiomOfChoice` to extract
a common renaming from a pointwise-varDiag substitution;
`scr_compositionality` is a sixteen-case diagram chase; `cr_fixpoint`
and `cr_induction` collapse to structural induction on `Tm`. The third
pass carries the two conceptually hard theorems: associativity of
substitution, whose ⇐-direction forces us to glue two intermediate
contexts into a dependent sum `Σ (x : Γ), G x` to fit the single-context
statement, and oplax compositionality, whose ⇒-direction uses
`Classical.axiomOfChoice` to select a shared intermediate substitution
at each variable. The section closes with the four axioms governing
`j`, which are immediate once one recognises `j` as the intersection of
the diagonal with "term is the weakening of a closed one".
-/

/-- The variable co-equivalence (paper: `Δη`): relates `t` and `s` iff
both are the same variable `Tm.var x`. Sees only variables and ignores
compound terms; serves as the two-sided identity of relation
substitution and is orthogonal to every compound-headed relation. -/
def varDiag : SynRel := {
  rel := fun Γ t s => ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩
}

/-- Strict compatible refinement (paper: `~φ`): relates `t` and `s`
iff they have the same outermost constructor and their immediate
sub-terms are pairwise `φ`-related. Four disjuncts, one per
constructor: `(zero, zero)` with no premise on `φ` (nullary intro),
`(succ t', succ s')` with `φ t' s'` (unary intro),
`(plus m₁ n₁, plus m₂ n₂)` and `(mult m₁ n₁, mult m₂ n₂)` with
pairwise-`φ` bodies (binary elim). The nullary case is precisely what
makes `scr ⊥ ≠ ⊥` and forces the non-empty-join relaxation of
`OperationalDecomposition` discussed in the module preamble. -/
def scr (φ : SynRel) : SynRel := {
  rel := fun Γ t s =>
    (t = Tm.zero ∧ s = Tm.zero) ∨
    (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ φ.rel Γ t' s') ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                            φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                            φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂)
  ren_closed := by
    intro Γ Δ f t s h
    rcases h with ⟨rfl, rfl⟩
                | ⟨t', s', rfl, rfl, hφ⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨t'.ren f, s'.ren f, rfl, rfl, φ.ren_closed f hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    rfl, rfl, φ.ren_closed f hφm, φ.ren_closed f hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    rfl, rfl, φ.ren_closed f hφm, φ.ren_closed f hφn⟩))
}

/-- Relation substitution (paper: `φ[ψ]`): relates `u` and `v` at
context Θ when there exist a source context Γ, terms `t s : Tm Γ` with
`φ.rel Γ t s`, and substitutions `τ σ : Γ → Tm Θ` with `τ x` and `σ x`
pointwise `ψ`-related, such that `u = t.subst τ` and `v = s.subst σ`.
The source context Γ is existentially quantified — a witness, not part
of the data — which is why associativity of `subst` needs to glue two
such witnesses into a dependent sum below. -/
def subst (φ ψ : SynRel) : SynRel := {
  rel := fun Θ u v =>
    ∃ (Γ : Type) (t s : Tm Γ) (τ σ : Γ → Tm Θ),
      u = t.subst τ ∧ v = s.subst σ
      ∧ φ.rel Γ t s ∧ ∀ x, ψ.rel Θ (τ x) (σ x)
  ren_closed := by
    intro Θ Θ' f u v h
    obtain ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩ := h
    refine ⟨Γ, t, s, fun x => (τ x).ren f, fun x => (σ x).ren f,
            ?_, ?_, hφ, fun x => ψ.ren_closed f (hψ x)⟩
    · rw [hu, Tm.ren_subst]
    · rw [hv, Tm.ren_subst]
}

/-!
Projection lemmas that unfold each of the three operations back to
their `Prop`-level content, tagged `@[simp]` for automated use.
-/

@[simp] theorem varDiag_rel {Γ} {t s : Tm Γ} :
    (varDiag : SynRel).rel Γ t s ↔ ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x :=
  Iff.rfl

@[simp] theorem scr_rel {φ : SynRel} {Γ} {t s : Tm Γ} :
    (scr φ).rel Γ t s ↔
      (t = Tm.zero ∧ s = Tm.zero) ∨
      (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ φ.rel Γ t' s') ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                              φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                              φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) := Iff.rfl

@[simp] theorem subst_rel {φ ψ : SynRel} {Θ} {u v : Tm Θ} :
    (subst φ ψ).rel Θ u v ↔
      ∃ (Γ : Type) (t s : Tm Γ) (τ σ : Γ → Tm Θ),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel Γ t s ∧ ∀ x, ψ.rel Θ (τ x) (σ x) := Iff.rfl

/-!
First pass — the axioms that discharge by unfolding definitions and
threading an existential through a constructor. No induction on `Tm`,
no appeal to choice, no gluing of contexts. Concretely: monotonicity of
`scr` and of `subst` in its right slot; commutation of `scr` and
`subst` with converse; join-preservation of `subst` in its left slot;
symmetry, co-transitivity, and disjointness of `varDiag` with the
compound layer `scr φ`.
-/

theorem scr_monotonicity {φ ψ : SynRel} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro Γ t s hs
  rcases hs with ⟨rfl, rfl⟩
              | ⟨t', s', rfl, rfl, hφ⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨t', s', rfl, rfl, h Γ t' s' hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                  h Γ m₁ m₂ hφm, h Γ n₁ n₂ hφn⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                  h Γ m₁ m₂ hφm, h Γ n₁ n₂ hφn⟩))

theorem subst_monotonicity_right {φ ψ ψ' : SynRel} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro Θ u v hs
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨Γ, t, s, τ, σ, hu, hv, hφ, fun x => h Θ (τ x) (σ x) (hψ x)⟩

theorem scr_converse_commutation (φ : SynRel) : scr (φᵒ) = (scr φ)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩
          | ⟨t', s', rfl, rfl, hφ⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨s', t', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))
  · rintro (⟨rfl, rfl⟩
          | ⟨t', s', rfl, rfl, hφ⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨s', t', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))

theorem subst_converse_commutation (φ ψ : SynRel) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

theorem subst_join_preservation_left (𝒮 : Set SynRel) (ψ : SynRel) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

theorem varDiag_symmetry : (varDiag : SynRel)ᵒ ≤ varDiag := by
  intro Γ t s h
  obtain ⟨x, hs, ht⟩ := h
  exact ⟨x, ht, hs⟩

theorem varDiag_cotransitivity : (varDiag : SynRel) ≤ varDiag * varDiag := by
  intro Γ t s h
  obtain ⟨x, ht, hs⟩ := h
  exact ⟨Tm.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

theorem varDiag_scr_orthogonality (φ : SynRel) :
    (varDiag : SynRel) * scr φ ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨x, _, rfl⟩, hscr⟩ := h
  rcases hscr with ⟨hu, _⟩
                | ⟨_, _, hu, _⟩
                | ⟨_, _, _, _, hu, _⟩
                | ⟨_, _, _, _, hu, _⟩ <;> cases hu

/-!
Second pass — proofs that need real work, though of a familiar kind.
`subst_varDiag_unit_right` extracts, via `Classical.axiomOfChoice`, a
common renaming from a pointwise-varDiag substitution. `subst_scr_oplaxity`
is a case-split over the four `scr`-cases. `scr_compositionality`
is a sixteen-case matrix: four constructor cases on each side, twelve
of which are shape-conflicts closed by `cases`, four of which are the
honest sub-proofs. `cr_fixpoint` and `cr_induction` together internalise
structural induction on `Tm` inside `SynRel`, matching the abstract law
`Δ̂ ≤ φ ⇒ Δ ≤ φ` of Section 3.1.1 of the paper.
-/

theorem subst_varDiag_unit_left (ψ : SynRel) : subst varDiag ψ = ψ := by
  ext Θ u v
  constructor
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨Unit, Tm.var (), Tm.var (), fun _ => u, fun _ => v,
            rfl, rfl, ⟨(), rfl, rfl⟩, ?_⟩
    intro _; exact hψ

theorem subst_varDiag_unit_right (φ : SynRel) : subst φ varDiag = φ := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, rfl, rfl, hφ, hvar⟩
    obtain ⟨ρ, hρ⟩ := Classical.axiomOfChoice hvar
    have hτ : τ = fun x => Tm.var (ρ x) := funext (fun x => (hρ x).1)
    have hσ : σ = fun x => Tm.var (ρ x) := funext (fun x => (hρ x).2)
    rw [hτ, hσ]
    exact φ.ren_closed ρ hφ
  · intro hφ
    exact ⟨Θ, u, v, Tm.var, Tm.var,
           (Tm.subst_id u).symm, (Tm.subst_id v).symm, hφ,
           fun x => ⟨x, rfl, rfl⟩⟩

theorem subst_scr_oplaxity (φ ψ : SynRel) :
    subst (scr φ) ψ ≤ scr (subst φ ψ) := by
  intro Θ u v h
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hscr, hψ⟩ := h
  rcases hscr with ⟨rfl, rfl⟩
                | ⟨t', s', rfl, rfl, hφ⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · exact Or.inl ⟨by rw [hu]; rfl, by rw [hv]; rfl⟩
  · refine Or.inr (Or.inl ⟨t'.subst τ, s'.subst σ,
                           by rw [hu]; rfl, by rw [hv]; rfl, ?_⟩)
    exact ⟨Γ, t', s', τ, σ, rfl, rfl, hφ, hψ⟩
  · refine Or.inr (Or.inr (Or.inl
      ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
       by rw [hu]; rfl, by rw [hv]; rfl, ?_, ?_⟩))
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, hφm, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hφn, hψ⟩
  · refine Or.inr (Or.inr (Or.inr
      ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
       by rw [hu]; rfl, by rw [hv]; rfl, ?_, ?_⟩))
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, hφm, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hφn, hψ⟩

theorem scr_compositionality (φ ψ : SynRel) : scr (φ * ψ) = scr φ * scr ψ := by
  ext Γ t v
  constructor
  · rintro (⟨rfl, rfl⟩
          | ⟨t', v', rfl, rfl, ⟨u, hφ, hψ⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨u_m, hφm, hψm⟩, ⟨u_n, hφn, hψn⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨u_m, hφm, hψm⟩, ⟨u_n, hφn, hψn⟩⟩)
    · exact ⟨Tm.zero, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Tm.succ u, Or.inr (Or.inl ⟨t', u, rfl, rfl, hφ⟩),
                        Or.inr (Or.inl ⟨u, v', rfl, rfl, hψ⟩)⟩
    · exact ⟨Tm.plus u_m u_n,
             Or.inr (Or.inr (Or.inl ⟨m₁, u_m, n₁, u_n, rfl, rfl, hφm, hφn⟩)),
             Or.inr (Or.inr (Or.inl ⟨u_m, m₂, u_n, n₂, rfl, rfl, hψm, hψn⟩))⟩
    · exact ⟨Tm.mult u_m u_n,
             Or.inr (Or.inr (Or.inr ⟨m₁, u_m, n₁, u_n, rfl, rfl, hφm, hφn⟩)),
             Or.inr (Or.inr (Or.inr ⟨u_m, m₂, u_n, n₂, rfl, rfl, hψm, hψn⟩))⟩
  · rintro ⟨w, h1, h2⟩
    rcases h1 with ⟨rfl, hw⟩
                | ⟨t', w', rfl, rfl, hφ⟩
                | ⟨m₁, wm, n₁, wn, rfl, rfl, hφm, hφn⟩
                | ⟨m₁, wm, n₁, wn, rfl, rfl, hφm, hφn⟩
    · -- w = zero
      subst hw
      rcases h2 with ⟨_, rfl⟩
                  | ⟨_, _, hw, _⟩
                  | ⟨_, _, _, _, hw, _⟩
                  | ⟨_, _, _, _, hw, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · cases hw
      · cases hw
      · cases hw
    · rcases h2 with ⟨hw, _⟩
                  | ⟨w'', v', hw, rfl, hψ⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
      · cases hw
      · have : w' = w'' := Tm.succ.inj hw
        subst this
        exact Or.inr (Or.inl ⟨t', v', rfl, rfl, ⟨w', hφ, hψ⟩⟩)
      · cases hw
      · cases hw
    · rcases h2 with ⟨hw, _⟩
                  | ⟨_, _, hw, _⟩
                  | ⟨wm', m₂, wn', n₂, hw, rfl, hψm, hψn⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
      · cases hw
      · cases hw
      · obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp hw
        subst hm; subst hn
        exact Or.inr (Or.inr (Or.inl
          ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, hφm, hψm⟩, ⟨wn, hφn, hψn⟩⟩))
      · cases hw
    · rcases h2 with ⟨hw, _⟩
                  | ⟨_, _, hw, _⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
                  | ⟨wm', m₂, wn', n₂, hw, rfl, hψm, hψn⟩
      · cases hw
      · cases hw
      · cases hw
      · obtain ⟨hm, hn⟩ := Tm.mult.injEq _ _ _ _ |>.mp hw
        subst hm; subst hn
        exact Or.inr (Or.inr (Or.inr
          ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, hφm, hψm⟩, ⟨wn, hφn, hψn⟩⟩))

theorem cr_fixpoint : (varDiag ⊔ scr 1 : SynRel) = 1 := by
  ext Γ t s
  constructor
  · intro h
    rcases h with ⟨x, rfl, rfl⟩
                | (⟨rfl, rfl⟩
                  | ⟨t', s', rfl, rfl, hφ⟩
                  | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
                  | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · rfl
    · rfl
    · exact congrArg Tm.succ hφ
    · exact congrArg₂ Tm.plus hφm hφn
    · exact congrArg₂ Tm.mult hφm hφn
  · intro (h : t = s)
    subst h
    cases t with
    | var x    => exact Or.inl ⟨x, rfl, rfl⟩
    | zero     => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | succ t'  => exact Or.inr (Or.inr (Or.inl ⟨t', t', rfl, rfl, rfl⟩))
    | plus m n => exact Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨m, m, n, n, rfl, rfl, rfl, rfl⟩)))
    | mult m n => exact Or.inr (Or.inr (Or.inr (Or.inr
                    ⟨m, m, n, n, rfl, rfl, rfl, rfl⟩)))

theorem cr_induction {φ : SynRel}
    (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
  intro Γ t s (heq : t = s)
  subst heq
  induction t with
  | var x =>
    exact h Γ (Tm.var x) (Tm.var x) (Or.inl ⟨x, rfl, rfl⟩)
  | zero =>
    exact h Γ Tm.zero Tm.zero (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | succ t' ih =>
    exact h Γ (Tm.succ t') (Tm.succ t')
      (Or.inr (Or.inr (Or.inl ⟨t', t', rfl, rfl, ih⟩)))
  | plus m n ihm ihn =>
    exact h Γ (Tm.plus m n) (Tm.plus m n)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, m, n, n, rfl, rfl, ihm, ihn⟩))))
  | mult m n ihm ihn =>
    exact h Γ (Tm.mult m n) (Tm.mult m n)
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, m, n, n, rfl, rfl, ihm, ihn⟩))))

/-!
Third pass — the two conceptually hard theorems. Associativity of
substitution states `subst (subst φ ψ) χ = subst φ (subst ψ χ)`, and
its ⇐-direction has to glue a Γ-indexed family of source contexts
`G : Γ → Type` into a single source context `Σ (x : Γ), G x` in order
to fit the shape of the LHS; this is the concrete face of the
"flatten a fibration" step of the categorical proof, and it is
unavoidable given the "contexts as types" decision. Oplax
compositionality states `subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ'`,
and its ⇒-direction uses `Classical.axiomOfChoice` to pick a *single*
intermediate substitution `μ` at each variable, closing the diagram
cleanly into the two halves of the target composition; the reverse
inequality fails in general, hence "oplax".
-/

theorem subst_associativity (φ ψ χ : SynRel) :
    subst (subst φ ψ) χ = subst φ (subst ψ χ) := by
  ext Δ u v
  constructor
  · rintro ⟨Γ₁, t₁, s₁, τ₁, σ₁, rfl, rfl, hφψ, hχ⟩
    obtain ⟨Γ₀, t₀, s₀, τ₀, σ₀, rfl, rfl, hφ, hψ⟩ := hφψ
    refine ⟨Γ₀, t₀, s₀, Subst.comp τ₀ τ₁, Subst.comp σ₀ σ₁,
            Tm.subst_comp t₀ τ₀ τ₁, Tm.subst_comp s₀ σ₀ σ₁, hφ, ?_⟩
    intro x
    exact ⟨Γ₁, τ₀ x, σ₀ x, τ₁, σ₁, rfl, rfl, hψ x, hχ⟩
  · rintro ⟨Γ, t, s, τ, σ, rfl, rfl, hφ, hpsichi⟩
    choose G TT SS TA SI hτ hσ hψ hχ using hpsichi
    let Γ' : Type := (x : Γ) × G x
    let inj : (x : Γ) → G x → Γ' := fun x y => ⟨x, y⟩
    let τ₀ : Γ → Tm Γ' := fun x => (TT x).ren (inj x)
    let σ₀ : Γ → Tm Γ' := fun x => (SS x).ren (inj x)
    let τ₁ : Γ' → Tm Δ := fun p => TA p.1 p.2
    let σ₁ : Γ' → Tm Δ := fun p => SI p.1 p.2
    refine ⟨Γ', t.subst τ₀, s.subst σ₀, τ₁, σ₁, ?_, ?_, ?_, ?_⟩
    · rw [Tm.subst_comp]
      congr 1
      funext x
      change τ x = ((TT x).ren (inj x)).subst τ₁
      rw [Tm.subst_ren]
      exact hτ x
    · rw [Tm.subst_comp]
      congr 1
      funext x
      change σ x = ((SS x).ren (inj x)).subst σ₁
      rw [Tm.subst_ren]
      exact hσ x
    · exact ⟨Γ, t, s, τ₀, σ₀, rfl, rfl, hφ,
             fun x => ψ.ren_closed (inj x) (hψ x)⟩
    · rintro ⟨x, y⟩
      exact hχ x y

theorem subst_compositionality_oplax (φ φ' ψ ψ' : SynRel) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro Δ u v h
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨Γ, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨Γ, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

/-!
The fourth SRA operation, `j`, distinguishes closed terms from open
ones inside the algebra: it relates `t` to `s` iff `t = s` and `t` is
the weakening of some `t₀ : ClosedTm`. As a `SynRel` it is a
coreflexive (a subset of the diagonal), supported on the image of
`Tm.close`. The four axioms below — coreflexivity, symmetry,
cotransitivity, and orthogonality with `varDiag` — are all immediate
from the definition, with the last one using that a closed term cannot
be a variable.
-/

/-- The closure constant (paper: `Δ_κ`): relates `t` to itself provided
`t` is the weakening of some `t₀ : ClosedTm`. A coreflexive supported
on the image of `Tm.close Γ : ClosedTm → Tm Γ`; the abstract `SRA.box`
modality is built from it, and the four axioms below are the bare
minimum for `box` to behave as a monotone comonad. -/
def j : SynRel := {
  rel := fun Γ t s => t = s ∧ ∃ t₀ : ClosedTm, t = Tm.close Γ t₀
  ren_closed := by
    intro Γ Δ f t s h
    obtain ⟨hts, t₀, ht⟩ := h
    refine ⟨by rw [hts], t₀, ?_⟩
    rw [ht, Tm.ren_close]
}

@[simp] theorem j_rel {Γ} {t s : Tm Γ} :
    (j : SynRel).rel Γ t s ↔
      t = s ∧ ∃ t₀ : ClosedTm, t = Tm.close Γ t₀ := Iff.rfl

theorem j_coreflexivity : (j : SynRel) ≤ 1 := fun _ _ _ h => h.1

theorem j_symmetry : (j : SynRel)ᵒ ≤ j := by
  intro Γ t s h
  obtain ⟨hst, t₀, hs⟩ := h
  exact ⟨hst.symm, t₀, hst.symm.trans hs⟩

theorem j_cotransitivity : (j : SynRel) ≤ j * j := by
  intro Γ t s h
  refine ⟨t, ⟨rfl, ?_⟩, h⟩
  obtain ⟨_, t₀, ht⟩ := h
  exact ⟨t₀, ht⟩

theorem j_varDiag_orthogonality : (j : SynRel) * varDiag ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩ := h
  subst htu; subst huvar
  cases t₀ with
  | var y   => exact y.elim
  | zero    => cases hcls
  | succ _  => cases hcls
  | plus _ _ => cases hcls
  | mult _ _ => cases hcls

end SynRel

/-!
The previous section did the work; here we simply collect it. The
`instance SRA SynRel` declaration is a form-filling exercise: for each
of the sixteen SRA fields we hand back the corresponding proof. From
this point on, every abstract lemma proved against a generic `SRA α` —
including the closure modality `SRA.box`, the combinator `SRA.cr`, and
eventually the bridge theorem itself — becomes a concrete lemma about
`SynRel`. The two lemmas that close the section are sanity checks:
`scr_top_ne_bot` witnesses that `SynRel` is non-degenerate, and
`substJClosed` verifies `SRA.IsClosed (subst a j)`, a technical fact
needed by `box_elimination_oplaxity` further down.
-/

instance instSRA : SRA SynRel where
  varDiag := SynRel.varDiag
  scr := SynRel.scr
  subst := SynRel.subst
  varDiag_symmetry := SynRel.varDiag_symmetry
  varDiag_cotransitivity := SynRel.varDiag_cotransitivity
  scr_monotonicity := fun _ _ h => SynRel.scr_monotonicity h
  scr_compositionality := SynRel.scr_compositionality
  scr_converse_commutation := SynRel.scr_converse_commutation
  varDiag_scr_orthogonality := SynRel.varDiag_scr_orthogonality
  subst_monotonicity_right := fun _ _ _ h => SynRel.subst_monotonicity_right h
  subst_compositionality_oplax := SynRel.subst_compositionality_oplax
  subst_converse_commutation := SynRel.subst_converse_commutation
  subst_join_preservation_left := SynRel.subst_join_preservation_left
  subst_varDiag_unit_left := SynRel.subst_varDiag_unit_left
  subst_varDiag_unit_right := SynRel.subst_varDiag_unit_right
  subst_associativity := SynRel.subst_associativity
  subst_scr_oplaxity := SynRel.subst_scr_oplaxity
  cr_fixpoint := SynRel.cr_fixpoint
  cr_induction := fun _ h => SynRel.cr_induction h
  j := SynRel.j
  j_coreflexivity := SynRel.j_coreflexivity
  j_symmetry := SynRel.j_symmetry
  j_cotransitivity := SynRel.j_cotransitivity
  j_varDiag_orthogonality := SynRel.j_varDiag_orthogonality

namespace SynRel

theorem scr_top_ne_bot : (scr ⊤ : SynRel) ≠ ⊥ := by
  intro hbad
  have h : (scr ⊤ : SynRel).rel Unit (Tm.succ (Tm.var ())) (Tm.succ (Tm.var ())) :=
    Or.inr (Or.inl ⟨Tm.var (), Tm.var (), rfl, rfl, trivial⟩)
  rw [hbad] at h; exact h

/-- Model-side verification of `SRA.IsClosed (subst a j)`. -/
theorem substJClosed (a : SynRel) : SRA.IsClosed (SynRel.subst a j) := by
  change SynRel.subst a j ≤ SRA.box (SynRel.subst a j)
  intro Θ u v hsubst
  have hsub := hsubst
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, _, hj⟩ := hsub
  have hτσ : ∀ x, τ x = σ x := fun x => (hj x).1
  have hτ_cls : ∀ x, ∃ t₀ : ClosedTm, τ x = Tm.close Θ t₀ :=
    fun x => (hj x).2
  obtain ⟨τ', hτ'eq⟩ := Classical.axiomOfChoice hτ_cls
  have hu_cls : (t.subst τ : Tm Θ) = Tm.close Θ (t.subst τ') := by
    change t.subst τ = (t.subst τ').ren Empty.elim
    rw [Tm.ren_subst]
    congr 1
    funext x
    exact hτ'eq x
  have hv_cls : (s.subst σ : Tm Θ) = Tm.close Θ (s.subst τ') := by
    change s.subst σ = (s.subst τ').ren Empty.elim
    rw [Tm.ren_subst]
    congr 1
    funext x
    rw [← hτσ x]
    exact hτ'eq x
  refine ⟨s.subst σ, ⟨t.subst τ,
          ⟨rfl, t.subst τ', hu_cls⟩,
          hsubst⟩,
          ⟨rfl, s.subst τ', hv_cls⟩⟩

end SynRel

/-!
`SynRel` is now a full-blown `SRA`. The next layer refines the strict
compatible refinement `scr` into its constructor slice `introduction`
and its destructor slice `elimination`, matching the paper's cocartesian
decomposition of `~·`. In our signature `introduction a` covers the two
constructor cases `(zero, zero)` and `(succ t', succ s')` — the first
carrying no premise on `a`, since `zero` is nullary — while
`elimination a b` covers the two destructor cases `(plus m₁ n₁, plus m₂ n₂)`
and `(mult m₁ n₁, mult m₂ n₂)`, with `a` on the major slot and `b` on
the minor. The fourteen axioms of `OperationalDecomposition` — join
preservation, compositionality and converse for each operation, oplax
unit laws, orthogonality of intro and elim, the decomposition
`scr a = introduction a ⊔ elimination a a`, and the three oplax laws
governing substitution and the closure modality — are then discharged
one at a time by the same kind of case-splitting that dominated
Section 3. The heaviest single proof is `box_elimination_oplaxity`,
which case-splits on all five `Tm` constructors for each of the two
closed-term slots. `introduction_join_preservation` carries the
`𝒮.Nonempty` hypothesis, the relaxation discussed in the module
preamble; without it the nullary `zero`-case would be inconsistent with
the empty-set instance of the axiom.
-/

namespace SynRel

/-- The constructor slice of `scr`. Two cases: `(zero, zero)` — nullary
intro form, no `a`-premise, and the case that forces the non-empty-join
relaxation of the framework axiom — and `(succ t', succ s')` with
`a t' s'`. No `plus` or `mult`; those live in `elimination` below, and
the two operations are orthogonal by construction. -/
def introduction (a : SynRel) : SynRel := {
  rel := fun Γ t s =>
    (t = Tm.zero ∧ s = Tm.zero) ∨
    (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ a.rel Γ t' s')
  ren_closed := by
    intro _ _ f _ _ h
    rcases h with ⟨rfl, rfl⟩ | ⟨t', s', ht, hs, ha⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨t'.ren f, s'.ren f, by rw [ht]; rfl, by rw [hs]; rfl,
                    a.ren_closed f ha⟩
}

/-- The destructor slice of `scr`. Two cases: `(plus m₁ n₁, plus m₂ n₂)`
with `a m₁ m₂` (major) and `b n₁ n₂` (minor), and
`(mult m₁ n₁, mult m₂ n₂)` with the same slot convention. Slot 0 is
major throughout, which is what makes the Gentzen principles below
speak of the left argument of `plus` and `mult` as the evaluated one. -/
def elimination (a b : SynRel) : SynRel := {
  rel := fun Γ t s =>
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                            a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂) ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                            a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂)
  ren_closed := by
    intro _ _ f _ _ h
    rcases h with ⟨m₁, m₂, n₁, n₂, ht, hs, ha, hb⟩
                | ⟨m₁, m₂, n₁, n₂, ht, hs, ha, hb⟩
    · exact Or.inl ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    by rw [ht]; rfl, by rw [hs]; rfl,
                    a.ren_closed f ha, b.ren_closed f hb⟩
    · exact Or.inr ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    by rw [ht]; rfl, by rw [hs]; rfl,
                    a.ren_closed f ha, b.ren_closed f hb⟩
}

@[simp] theorem introduction_rel {a : SynRel} {Γ} {t s : Tm Γ} :
    (introduction a).rel Γ t s ↔
      (t = Tm.zero ∧ s = Tm.zero) ∨
      (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ a.rel Γ t' s') :=
  Iff.rfl

@[simp] theorem elimination_rel {a b : SynRel} {Γ} {t s : Tm Γ} :
    (elimination a b).rel Γ t s ↔
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                              a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂) ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                              a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂) := Iff.rfl

/-!
The three semirelator axioms for each of `introduction` and
`elimination`: join preservation, compositionality, and converse
commutation. Nine theorems in total; the pattern is uniform, differing
only in which constructor case is being propagated through which
operation.
-/

theorem introduction_join_preservation (𝒮 : Set SynRel) (h𝒮 : 𝒮.Nonempty) :
    introduction (sSup 𝒮) = sSup (introduction '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩)
    · -- zero case: pick any witness in 𝒮 to place the derivation.
      obtain ⟨φ, hφ𝒮⟩ := h𝒮
      exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, Or.inr ⟨t', s', rfl, rfl, hφ⟩⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, hφ⟩
    rcases hφ with ⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, hφ⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩

theorem introduction_compositionality (a b : SynRel) :
    introduction (a * b) = introduction a * introduction b := by
  ext Γ t v
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨t', v', rfl, rfl, u', ha, hb⟩)
    · exact ⟨Tm.zero, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Tm.succ u',
             Or.inr ⟨t', u', rfl, rfl, ha⟩,
             Or.inr ⟨u', v', rfl, rfl, hb⟩⟩
  · rintro ⟨u, h1, h2⟩
    rcases h1 with ⟨rfl, hu⟩ | ⟨t', u₁, rfl, hu, ha⟩
    · -- u = zero
      subst hu
      rcases h2 with ⟨_, rfl⟩ | ⟨_, _, hu, _, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · cases hu
    · rcases h2 with ⟨hu', _⟩ | ⟨u₂, v', hu', rfl, hb⟩
      · cases hu.symm.trans hu'
      · have hu12 : u₁ = u₂ := Tm.succ.inj (hu.symm.trans hu')
        refine Or.inr ⟨t', v', rfl, rfl, u₁, ha, ?_⟩
        rw [hu12]; exact hb

theorem introduction_converse_commutation (a : SynRel) :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, ha⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨s', t', rfl, rfl, ha⟩
  · rintro (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, ha⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨s', t', rfl, rfl, ha⟩

theorem elimination_join_preservation_left (𝒮 : Set SynRel) (b : SynRel) :
    elimination (sSup 𝒮) b = sSup ((fun a => elimination a b) '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩)
    · exact ⟨elimination φ b, ⟨φ, hφ𝒮, rfl⟩,
             Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩⟩
    · exact ⟨elimination φ b, ⟨φ, hφ𝒮, rfl⟩,
             Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, h⟩
    rcases h with ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩
    · exact Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
    · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩

theorem elimination_join_preservation_right (a : SynRel) (𝒮 : Set SynRel) :
    elimination a (sSup 𝒮) = sSup ((fun b => elimination a b) '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩)
    · exact ⟨elimination a φ, ⟨φ, hφ𝒮, rfl⟩,
             Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩⟩
    · exact ⟨elimination a φ, ⟨φ, hφ𝒮, rfl⟩,
             Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, h⟩
    rcases h with ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩
    · exact Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩
    · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩

theorem elimination_compositionality (a₁ a₂ b₁ b₂ : SynRel) :
    elimination (a₁ * a₂) (b₁ * b₂) = elimination a₁ b₁ * elimination a₂ b₂ := by
  ext Γ t v
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, ha₁, ha₂⟩, ⟨wn, hb₁, hb₂⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, ha₁, ha₂⟩, ⟨wn, hb₁, hb₂⟩⟩)
    · exact ⟨Tm.plus wm wn,
             Or.inl ⟨m₁, wm, n₁, wn, rfl, rfl, ha₁, hb₁⟩,
             Or.inl ⟨wm, m₂, wn, n₂, rfl, rfl, ha₂, hb₂⟩⟩
    · exact ⟨Tm.mult wm wn,
             Or.inr ⟨m₁, wm, n₁, wn, rfl, rfl, ha₁, hb₁⟩,
             Or.inr ⟨wm, m₂, wn, n₂, rfl, rfl, ha₂, hb₂⟩⟩
  · rintro ⟨u, h1, h2⟩
    rcases h1 with ⟨m₁, um, n₁, un, rfl, hu, ha₁, hb₁⟩
                | ⟨m₁, um, n₁, un, rfl, hu, ha₁, hb₁⟩
    · rcases h2 with ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
                  | ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
      · have heq : Tm.plus um un = Tm.plus um' un' := hu.symm.trans hu'
        obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
        subst hm; subst hn
        exact Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                      ⟨um, ha₁, ha₂⟩, ⟨un, hb₁, hb₂⟩⟩
      · cases hu.symm.trans hu'
    · rcases h2 with ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
                  | ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
      · cases hu.symm.trans hu'
      · have heq : Tm.mult um un = Tm.mult um' un' := hu.symm.trans hu'
        obtain ⟨hm, hn⟩ := Tm.mult.injEq _ _ _ _ |>.mp heq
        subst hm; subst hn
        exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                      ⟨um, ha₁, ha₂⟩, ⟨un, hb₁, hb₂⟩⟩

theorem elimination_converse_commutation (a b : SynRel) :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩)
    · exact Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
    · exact Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩)
    · exact Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
    · exact Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩

/-!
Oplax unit laws for both operations, orthogonality (a constructor
composed with a destructor is `⊥`), and the decomposition equality
`scr a = introduction a ⊔ elimination a a` that certifies our two
slices really do add up to the strict compatible refinement.
-/

theorem introduction_unit_oplaxity : (introduction 1 : SynRel) ≤ 1 := by
  rintro Γ t s (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, (heq : t' = s')⟩)
  · rfl
  · exact congrArg Tm.succ heq

theorem elimination_unit_oplaxity : (elimination 1 1 : SynRel) ≤ 1 := by
  rintro Γ t s (⟨m₁, m₂, n₁, n₂, rfl, rfl, (hm : m₁ = m₂), (hn : n₁ = n₂)⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, (hm : m₁ = m₂), (hn : n₁ = n₂)⟩)
  · exact congrArg₂ Tm.plus hm hn
  · exact congrArg₂ Tm.mult hm hn

theorem introduction_elimination_orthogonality (a b c : SynRel) :
    introduction a * elimination b c ≤ ⊥ := by
  rintro Γ t v ⟨u, h1, h2⟩
  rcases h1 with ⟨rfl, hu⟩ | ⟨t', u', rfl, hu, _⟩
  · -- u = zero
    subst hu
    rcases h2 with ⟨_, _, _, _, hu, _, _, _⟩ | ⟨_, _, _, _, hu, _, _, _⟩ <;> cases hu
  · rcases h2 with ⟨_, _, _, _, hu', _, _, _⟩ | ⟨_, _, _, _, hu', _, _, _⟩ <;>
      exact absurd (hu.symm.trans hu') (by intro h; cases h)

theorem scr_decomposition (a : SynRel) :
    (SRA.scr a : SynRel) = introduction a ⊔ elimination a a := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩
          | ⟨t', s', rfl, rfl, hφ⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨t', s', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inr (Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
  · rintro ((⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, hφ⟩)
          | (⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩))
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨t', s', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩))

/-!
The three oplax laws relating the intro / elim decomposition to
substitution and to the closure modality `SRA.box`.
`box_elimination_oplaxity` is the technically heaviest theorem of the
section: it requires a full five-way case-split on the closed term
underlying the elimination form's major argument.
-/

theorem subst_introduction_oplaxity (a b : SynRel) :
    subst (introduction a) b ≤ introduction (subst a b) := by
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, hintro, hψ⟩
  rcases hintro with ⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, ha⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨t'.subst τ, s'.subst σ, rfl, rfl, ?_⟩
    exact ⟨Γ, t', s', τ, σ, rfl, rfl, ha, hψ⟩

theorem subst_elimination_oplaxity (a b c : SynRel) :
    subst (elimination a b) c ≤ elimination (subst a c) (subst b c) := by
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, helim, hψ⟩
  rcases helim with ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
  · refine Or.inl ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
                   rfl, rfl, ?_, ?_⟩
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, ha, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hb, hψ⟩
  · refine Or.inr ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
                   rfl, rfl, ?_, ?_⟩
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, ha, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hb, hψ⟩

theorem box_elimination_oplaxity (a b : SynRel) :
    (SRA.box (elimination a b) : SynRel) ≤ elimination (SRA.box a) b := by
  intro Θ u v h
  obtain ⟨w, hjeab, hjwv⟩ := h
  obtain ⟨w', hju, hab⟩ := hjeab
  obtain ⟨huw', u₀, hu_close⟩ := hju
  subst huw'
  obtain ⟨hwv, v₀, hv_close⟩ := hjwv
  subst hwv
  rcases hab with ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, hab_maj, hab_min⟩
                | ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, hab_maj, hab_min⟩
  · -- plus branch: `close Θ u₀ = plus m₁ n₁`
    cases u₀ with
    | var x => exact x.elim
    | zero =>
      have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | succ _ =>
      have : Tm.close Θ (Tm.succ _) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | plus u₀m u₀n =>
      have hu_shape :
          Tm.plus (Tm.close Θ u₀m) (Tm.close Θ u₀n) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      obtain ⟨hm_eq, hn_eq⟩ := Tm.plus.injEq _ _ _ _ |>.mp hu_shape
      cases v₀ with
      | var x => exact x.elim
      | zero =>
        have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | succ _ =>
        have : Tm.close Θ (Tm.succ _) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | plus v₀m v₀n =>
        have hv_shape :
            Tm.plus (Tm.close Θ v₀m) (Tm.close Θ v₀n) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        obtain ⟨hm_eq', hn_eq'⟩ := Tm.plus.injEq _ _ _ _ |>.mp hv_shape
        refine Or.inl ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, ?_, hab_min⟩
        refine ⟨m₂, ⟨m₁, ⟨rfl, u₀m, hm_eq.symm⟩, hab_maj⟩,
                ⟨rfl, v₀m, hm_eq'.symm⟩⟩
      | mult v₀m v₀n =>
        have : Tm.close Θ (Tm.mult _ _) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
    | mult _ _ =>
      have : Tm.close Θ (Tm.mult _ _) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
  · -- mult branch: `close Θ u₀ = mult m₁ n₁`
    cases u₀ with
    | var x => exact x.elim
    | zero =>
      have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | succ _ =>
      have : Tm.close Θ (Tm.succ _) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | plus _ _ =>
      have : Tm.close Θ (Tm.plus _ _) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | mult u₀m u₀n =>
      have hu_shape :
          Tm.mult (Tm.close Θ u₀m) (Tm.close Θ u₀n) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      obtain ⟨hm_eq, hn_eq⟩ := Tm.mult.injEq _ _ _ _ |>.mp hu_shape
      cases v₀ with
      | var x => exact x.elim
      | zero =>
        have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | succ _ =>
        have : Tm.close Θ (Tm.succ _) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | plus _ _ =>
        have : Tm.close Θ (Tm.plus _ _) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | mult v₀m v₀n =>
        have hv_shape :
            Tm.mult (Tm.close Θ v₀m) (Tm.close Θ v₀n) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        obtain ⟨hm_eq', hn_eq'⟩ := Tm.mult.injEq _ _ _ _ |>.mp hv_shape
        refine Or.inr ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, ?_, hab_min⟩
        refine ⟨m₂, ⟨m₁, ⟨rfl, u₀m, hm_eq.symm⟩, hab_maj⟩,
                ⟨rfl, v₀m, hm_eq'.symm⟩⟩

end SynRel

/-!
Assembly of the fourteen theorems above into the
`OperationalDecomposition SynRel` instance. The two join-preservation
fields require passing the `𝒮.Nonempty` proof through the wrapper
lambda; the other twelve are direct.
-/

instance instOperationalDecomposition : OperationalDecomposition SynRel where
  introduction := SynRel.introduction
  elimination := SynRel.elimination
  introduction_join_preservation 𝒮 h𝒮 :=
    SynRel.introduction_join_preservation 𝒮 h𝒮
  elimination_join_preservation_left := fun 𝒮 _ b =>
    SynRel.elimination_join_preservation_left 𝒮 b
  elimination_join_preservation_right := fun a 𝒮 _ =>
    SynRel.elimination_join_preservation_right a 𝒮
  introduction_compositionality := SynRel.introduction_compositionality
  introduction_converse_commutation := SynRel.introduction_converse_commutation
  elimination_compositionality := SynRel.elimination_compositionality
  elimination_converse_commutation := SynRel.elimination_converse_commutation
  introduction_unit_oplaxity := SynRel.introduction_unit_oplaxity
  elimination_unit_oplaxity := SynRel.elimination_unit_oplaxity
  introduction_elimination_orthogonality := SynRel.introduction_elimination_orthogonality
  scr_decomposition := SynRel.scr_decomposition
  subst_introduction_oplaxity := SynRel.subst_introduction_oplaxity
  subst_elimination_oplaxity := SynRel.subst_elimination_oplaxity
  box_elimination_oplaxity := SynRel.box_elimination_oplaxity

/-!
Everything above was preparation. We can now state the primitive
reduction of Peano arithmetic as a `SynRel`: the disjunction of the
four defining rewrite rules, `plus(zero, n) → n`,
`plus(succ m, n) → succ (plus m n)`, `mult(zero, n) → zero`, and
`mult(succ m, n) → plus (mult m n) n`. Renaming-closure of the family
is checked by mapping the free variables of each pattern under the
renaming, a computation of one line per disjunct.

The next five theorems discharge, on this concrete `rule`, the five
local hypotheses required by the abstract bridge theorem
`local_confluence`. `IsReduction` states that a variable cannot reduce,
which is immediate since every rule pattern has a compound left-hand
side. `IsSubstitutiveAtIdentity` states that the rule is preserved by
substitution along a pointwise-equal substitution; it splits into four
cases, each a small `Tm.subst` computation. `IsDeterministic` states
that the four rule patterns are pairwise non-overlapping, which gives
a 4×4 = 16 sub-case matrix with twelve shape-conflicts and four honest
sub-cases. `GIP` (Gentzen's Inversion Principle) picks, for each of the
four rule patterns, the redex itself as the witness of
`elimination (introduction 1) 1`, since every rule LHS is an
elimination form on an introduction-form major. `GCP` (Gentzen's
Conservation Principle) is the technically heaviest of the five: it
splits on 2 (elim-plus / elim-mult) × 4 (rule patterns) = 8 sub-cases,
four of which are immediate shape-conflicts (an elim-plus followed by
a mult-rule and vice versa), and four of which need real work — the
two "succ-side" ones use a `Bool` context to encode a two-slot
substitution template, while the two "zero-side" ones get away with a
trivial one-slot substitution over `Unit`. Once all five hold, the
bridge theorem delivers confluence of parallel reduction as a
one-liner: `rule_confluent := local_confluence rule_isReduction …`.
-/

namespace SynRel

/-- The primitive reduction: the four Peano defining equations,
```
plus(zero,   n) → n
plus(succ m, n) → succ (plus m n)
mult(zero,   n) → zero
mult(succ m, n) → plus (mult m n) n
```
packaged as a single `SynRel` by disjunction. All five bridge-theorem
hypotheses below (`IsReduction`, `IsSubstitutiveAtIdentity`,
`IsDeterministic`, `GIP`, `GCP`) are stated against this `SynRel` and
proceed by `rcases` on the disjunction. -/
def rule : SynRel := {
  rel := fun Γ t s =>
    (∃ n : Tm Γ, t = Tm.plus Tm.zero n ∧ s = n) ∨
    (∃ x y : Tm Γ, t = Tm.plus (Tm.succ x) y ∧ s = Tm.succ (Tm.plus x y)) ∨
    (∃ n : Tm Γ, t = Tm.mult Tm.zero n ∧ s = Tm.zero) ∨
    (∃ x y : Tm Γ, t = Tm.mult (Tm.succ x) y ∧
                    s = Tm.plus (Tm.mult x y) y)
  ren_closed := by
    intro Γ Δ f t s h
    rcases h with ⟨n, ht, hs⟩
                | ⟨x, y, ht, hs⟩
                | ⟨n, ht, hs⟩
                | ⟨x, y, ht, hs⟩
    · refine Or.inl ⟨n.ren f, ?_, ?_⟩
      · rw [ht]; simp
      · rw [hs]
    · refine Or.inr (Or.inl ⟨x.ren f, y.ren f, ?_, ?_⟩)
      · rw [ht]; simp
      · rw [hs]; simp
    · refine Or.inr (Or.inr (Or.inl ⟨n.ren f, ?_, ?_⟩))
      · rw [ht]; simp
      · rw [hs]; simp
    · refine Or.inr (Or.inr (Or.inr ⟨x.ren f, y.ren f, ?_, ?_⟩))
      · rw [ht]; simp
      · rw [hs]; simp
}

@[simp] theorem rule_rel {Γ} {t s : Tm Γ} :
    (rule : SynRel).rel Γ t s ↔
      (∃ n : Tm Γ, t = Tm.plus Tm.zero n ∧ s = n) ∨
      (∃ x y : Tm Γ, t = Tm.plus (Tm.succ x) y ∧
                      s = Tm.succ (Tm.plus x y)) ∨
      (∃ n : Tm Γ, t = Tm.mult Tm.zero n ∧ s = Tm.zero) ∨
      (∃ x y : Tm Γ, t = Tm.mult (Tm.succ x) y ∧
                      s = Tm.plus (Tm.mult x y) y) := Iff.rfl

theorem rule_isReduction : LeanTra.Confluence.IsReduction (rule : SynRel) := by
  change (SRA.varDiag * rule : SynRel) = ⊥
  ext Γ t v
  constructor
  · rintro ⟨m, ⟨z, rfl, rfl⟩, hrule⟩
    rcases hrule with ⟨_, hm, _⟩
                    | ⟨_, _, hm, _⟩
                    | ⟨_, hm, _⟩
                    | ⟨_, _, hm, _⟩ <;> cases hm
  · intro h; exact h.elim

theorem rule_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (rule : SynRel) := by
  change (SRA.subst rule 1 : SynRel) ≤ rule
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, hrule, hτσ⟩
  have hτσ_eq : τ = σ := funext hτσ
  subst hτσ_eq
  rcases hrule with ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
                  | ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
  · refine Or.inl ⟨n.subst τ, ?_, ?_⟩
    · rw [ht]; simp
    · rw [hs]
  · refine Or.inr (Or.inl ⟨x.subst τ, y.subst τ, ?_, ?_⟩)
    · rw [ht]; simp
    · rw [hs]; simp
  · refine Or.inr (Or.inr (Or.inl ⟨n.subst τ, ?_, ?_⟩))
    · rw [ht]; simp
    · rw [hs]; simp
  · refine Or.inr (Or.inr (Or.inr ⟨x.subst τ, y.subst τ, ?_, ?_⟩))
    · rw [ht]; simp
    · rw [hs]; simp

theorem rule_isDeterministic : LeanTra.Algebra.IsDeterministic (rule : SynRel) := by
  change ((rule : SynRel)ᵒ * rule) ≤ 1
  rintro Γ t t' ⟨m, h1, h2⟩
  -- h1 : rule^o (t, m) = rule (m, t); h2 : rule (m, t').
  -- 4 × 4 = 16 sub-cases; the diagonal ones give t = t', the off-diagonal
  -- ones contradict the shape of `m`.
  rcases h1 with ⟨n, hm_eq, rfl⟩
              | ⟨x, y, hm_eq, rfl⟩
              | ⟨n, hm_eq, rfl⟩
              | ⟨x, y, hm_eq, rfl⟩ <;>
    rcases h2 with ⟨n', hm_eq', rfl⟩
                | ⟨x', y', hm_eq', rfl⟩
                | ⟨n', hm_eq', rfl⟩
                | ⟨x', y', hm_eq', rfl⟩
  -- (plus-zero, plus-zero)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨_, rfl⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    rfl
  -- (plus-zero, plus-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    cases hz
  -- (plus-zero, mult-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (plus-zero, mult-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (plus-succ, plus-zero)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    cases hz
  -- (plus-succ, plus-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hs, rfl⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    have : x = x' := Tm.succ.inj hs
    subst this; rfl
  -- (plus-succ, mult-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (plus-succ, mult-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-zero, plus-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-zero, plus-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-zero, mult-zero)
  · rfl
  -- (mult-zero, mult-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.mult.injEq _ _ _ _ |>.mp this
    cases hz
  -- (mult-succ, plus-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-succ, plus-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-succ, mult-zero)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.mult.injEq _ _ _ _ |>.mp this
    cases hz
  -- (mult-succ, mult-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hs, rfl⟩ := Tm.mult.injEq _ _ _ _ |>.mp this
    have : x = x' := Tm.succ.inj hs
    subst this; rfl

theorem rule_gip : LeanTra.Metatheory.GIP (rule : SynRel) := by
  intro Γ t s hrule
  rcases hrule with ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
                  | ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
  · -- plus-zero: intermediate = t = plus zero n.
    subst ht; subst hs
    exact ⟨Tm.plus Tm.zero s,
           Or.inl ⟨Tm.zero, Tm.zero, s, s, rfl, rfl,
                   Or.inl ⟨rfl, rfl⟩, rfl⟩,
           Or.inl ⟨s, rfl, rfl⟩⟩
  · -- plus-succ: intermediate = t = plus (succ x) y.
    subst ht; subst hs
    exact ⟨Tm.plus (Tm.succ x) y,
           Or.inl ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           Or.inr (Or.inl ⟨x, y, rfl, rfl⟩)⟩
  · -- mult-zero: intermediate = t = mult zero n.
    subst ht; subst hs
    exact ⟨Tm.mult Tm.zero n,
           Or.inr ⟨Tm.zero, Tm.zero, n, n, rfl, rfl,
                   Or.inl ⟨rfl, rfl⟩, rfl⟩,
           Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))⟩
  · -- mult-succ: intermediate = t = mult (succ x) y.
    subst ht; subst hs
    exact ⟨Tm.mult (Tm.succ x) y,
           Or.inr ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           Or.inr (Or.inr (Or.inr ⟨x, y, rfl, rfl⟩))⟩

theorem rule_gcp : LeanTra.Metatheory.GCP (rule : SynRel) := by
  intro rx hcompat
  change (OperationalDecomposition.elimination (SRA.cr rx) rx : SynRel)
           * (rule : SynRel)
       ≤ (rule : SynRel) * SRA.subst rx rx
  -- Compatibility gives rx-reflexivity on any `t`, since `varDiag ⊔ scr rx ≤ rx`
  -- and by structural induction on `t` we cover every case.
  have hvar_refl : ∀ (Γ : Type) (x : Γ), rx.rel Γ (Tm.var x) (Tm.var x) :=
    fun _ x => hcompat _ _ _ (Or.inl ⟨x, rfl, rfl⟩)
  have hzero_refl : ∀ (Γ : Type), rx.rel Γ Tm.zero Tm.zero :=
    fun _ => hcompat _ _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  rintro Γ t v ⟨m, helim, hrule⟩
  rcases helim with ⟨m₁, m₂, n₁, n₂, rfl, hm_eq, hmaj, hmin⟩
                  | ⟨m₁, m₂, n₁, n₂, rfl, hm_eq, hmaj, hmin⟩
  -- ELIM-PLUS branch: t = plus m₁ n₁, m = plus m₂ n₂
  · rcases hrule with ⟨n_ru, hm_ru, hv⟩
                    | ⟨x', y', hm_ru, hv⟩
                    | ⟨_, hm_ru, _⟩
                    | ⟨_, _, hm_ru, _⟩
    · -- plus-zero rule: m₂ = zero, n₂ = n_ru, v = n_ru
      -- `subst hv` eliminates `n_ru` (Lean prefers to substitute the
      -- pattern-bound existential witness); `v` is what survives.
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold SRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨hm1, _⟩
                      | ⟨_, _, _, hz, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · -- m₁ = zero, t = plus zero n₁, reduce via plus-zero to n₁
          subst hm1
          refine ⟨n₁, Or.inl ⟨n₁, rfl, rfl⟩, ?_⟩
          -- subst rx rx (n₁, v) via the trivial `Unit` context.
          -- After `subst hv` earlier, `n_ru` was eliminated and `v` is
          -- what identifies the target minor slot.
          refine ⟨Unit, Tm.var (), Tm.var (),
                  fun _ => n₁, fun _ => _, rfl, rfl,
                  hvar_refl _ (), fun _ => hmin⟩
        · cases hz
        · cases hz
        · cases hz
    · -- plus-succ rule: m₂ = succ x', n₂ = y'
      -- `subst hv` eliminates `v` (LHS-var, RHS compound). `subst hn2`
      -- with `hn2 : n₂ = y'` eliminates `y'` (pattern-bound); `n₂`
      -- survives. Likewise `subst hxu'` with `hxu' : x' = u'` eliminates
      -- `u'`; `x'` survives.
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold SRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨_, hz⟩
                      | ⟨u, u', hm1_eq, hux, hrx⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · cases hz
        · -- m₁ = succ u, succ x' = succ u'; note y' → n₂ and u' → x'
          subst hm1_eq
          have hxu' : x' = u' := Tm.succ.inj hux
          subst hxu'
          refine ⟨Tm.succ (Tm.plus u n₁),
                  Or.inr (Or.inl ⟨u, n₁, rfl, rfl⟩), ?_⟩
          -- Bool context: false ↦ major body, true ↦ minor
          refine ⟨Bool,
                  Tm.succ (Tm.plus (Tm.var false) (Tm.var true)),
                  Tm.succ (Tm.plus (Tm.var false) (Tm.var true)),
                  fun b : Bool => if b then n₁ else u,
                  fun b : Bool => if b then n₂ else x',
                  rfl, rfl, ?_, ?_⟩
          · have h_scr_plus :
                (SRA.scr rx : SynRel).rel Bool
                  (Tm.plus (Tm.var false) (Tm.var true))
                  (Tm.plus (Tm.var false) (Tm.var true)) :=
              Or.inr (Or.inr (Or.inl
                ⟨_, _, _, _, rfl, rfl, hvar_refl _ _, hvar_refl _ _⟩))
            have h_rx_plus := hcompat _ _ _ (Or.inr h_scr_plus)
            have h_scr_succ :
                (SRA.scr rx : SynRel).rel Bool
                  (Tm.succ (Tm.plus (Tm.var false) (Tm.var true)))
                  (Tm.succ (Tm.plus (Tm.var false) (Tm.var true))) :=
              Or.inr (Or.inl ⟨_, _, rfl, rfl, h_rx_plus⟩)
            exact hcompat _ _ _ (Or.inr h_scr_succ)
          · intro b
            cases b <;> simp [*]
        · cases hz
        · cases hz
    · -- mult-zero rule but plus intermediate: impossible
      cases hm_eq.symm.trans hm_ru
    · -- mult-succ: impossible
      cases hm_eq.symm.trans hm_ru
  -- ELIM-MULT branch: t = mult m₁ n₁, m = mult m₂ n₂
  · rcases hrule with ⟨_, hm_ru, _⟩
                    | ⟨_, _, hm_ru, _⟩
                    | ⟨n_ru, hm_ru, hv⟩
                    | ⟨x', y', hm_ru, hv⟩
    · cases hm_eq.symm.trans hm_ru
    · cases hm_eq.symm.trans hm_ru
    · -- mult-zero rule: m₂ = zero, n₂ = n_ru, v = zero
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.mult.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold SRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨hm1, _⟩
                      | ⟨_, _, _, hz, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · -- m₁ = zero, t = mult zero n₁, reduce via mult-zero to zero
          subst hm1
          refine ⟨Tm.zero,
                  Or.inr (Or.inr (Or.inl ⟨n₁, rfl, rfl⟩)), ?_⟩
          -- subst rx rx (zero, zero) via closed constant
          exact ⟨Unit, Tm.zero, Tm.zero,
                 fun _ => Tm.zero, fun _ => Tm.zero, rfl, rfl,
                 hzero_refl _, fun _ => hzero_refl _⟩
        · cases hz
        · cases hz
        · cases hz
    · -- mult-succ rule: m₂ = succ x', n₂ = y'
      -- Same substitution convention as the plus-succ branch: `y' → n₂`,
      -- `u' → x'`.
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.mult.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold SRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨_, hz⟩
                      | ⟨u, u', hm1_eq, hux, hrx⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · cases hz
        · -- m₁ = succ u, succ x' = succ u'
          subst hm1_eq
          have hxu' : x' = u' := Tm.succ.inj hux
          subst hxu'
          refine ⟨Tm.plus (Tm.mult u n₁) n₁,
                  Or.inr (Or.inr (Or.inr ⟨u, n₁, rfl, rfl⟩)), ?_⟩
          -- Bool context: false ↦ major body, true ↦ minor (also
          -- reappears in outer plus's minor slot)
          refine ⟨Bool,
                  Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true),
                  Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true),
                  fun b : Bool => if b then n₁ else u,
                  fun b : Bool => if b then n₂ else x',
                  rfl, rfl, ?_, ?_⟩
          · have h_scr_mult :
                (SRA.scr rx : SynRel).rel Bool
                  (Tm.mult (Tm.var false) (Tm.var true))
                  (Tm.mult (Tm.var false) (Tm.var true)) :=
              Or.inr (Or.inr (Or.inr
                ⟨_, _, _, _, rfl, rfl, hvar_refl _ _, hvar_refl _ _⟩))
            have h_rx_mult := hcompat _ _ _ (Or.inr h_scr_mult)
            have h_scr_plus :
                (SRA.scr rx : SynRel).rel Bool
                  (Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true))
                  (Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true)) :=
              Or.inr (Or.inr (Or.inl
                ⟨_, _, _, _, rfl, rfl, h_rx_mult, hvar_refl _ _⟩))
            exact hcompat _ _ _ (Or.inr h_scr_plus)
          · intro b
            cases b <;> simp [*]
        · cases hz
        · cases hz

/-- Confluence of parallel reduction on the entire four-rule
Peano-arithmetic reduction system. Obtained by feeding the five local
hypotheses proved above to the abstract bridge theorem
`local_confluence`; no Peano-specific tactic appears in the body. -/
theorem rule_confluent :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (rule : SynRel)) :=
  LeanTra.Confluence.local_confluence
    rule_isReduction
    rule_isSubstitutiveAtIdentity
    rule_isDeterministic
    rule_gip
    rule_gcp

/-! ### Determinism of big-step evaluation

The metatheorem `LeanTra.Determinism.bigStep_determinism` concludes
`(a^⇓)ᵒ * a^⇓ ≤ Δκ` from `GIP`, `IsClosed` and `IsDeterministic` of
the rule. Plain `rule` does not satisfy `IsClosed`: it fires between
open terms too — e.g. `plus zero (var x)` with `x` free reduces to
`var x`. The natural instantiation is on the closed part of the
rule, `SRA.box rule`, which relates only closed terms; its three
hypotheses are discharged here. `IsClosed (SRA.box rule)` is
`SRA.box_isClosed`. `IsDeterministic (SRA.box rule)` follows from
`rule_isDeterministic` and `SRA.box_le`. `GIP (SRA.box rule)` is
proved directly by the same four-way case analysis as `rule_gip`,
adapted to carry the closedness bookkeeping through the two `j`
factors of `SRA.box`. The final theorem `rule_bigStep_determinism`
is then a one-line application of the metatheorem. -/

/-- Gentzen inversion for the closed part of the rule: every closed
step factors on the left through an elimination with an introduction
form in the major slot, with the closedness of the source preserved.
Same four-case argument as `rule_gip`, threading closedness through
the two `j` factors of `SRA.box`. -/
theorem rule_boxed_gip : LeanTra.Metatheory.GIP (SRA.box (rule : SynRel)) := by
  rintro Γ t s ⟨w, ⟨w', ⟨rfl, t₀, ht_close⟩, hrule⟩, ⟨rfl, s₀, hs_close⟩⟩
  -- Preserve `hs`/`hs'`/etc. as equational hypotheses instead of substituting
  -- them away: the plus-zero and mult-zero cases have `s = n` with `n` and `s`
  -- both fresh, and Lean's `subst` heuristic on that pair renames the surviving
  -- variable in a way that makes the term-level witness unreadable.
  rcases hrule with ⟨n, rfl, hs⟩
                  | ⟨x, y, rfl, rfl⟩
                  | ⟨n, rfl, hs⟩
                  | ⟨x, y, rfl, rfl⟩
  · -- plus-zero: source `plus zero n`, target `n` (via `hs : s = n`).
    refine ⟨Tm.plus Tm.zero n,
            Or.inl ⟨Tm.zero, Tm.zero, n, n, rfl, rfl,
                    Or.inl ⟨rfl, rfl⟩, rfl⟩,
            ⟨n,
              ⟨Tm.plus Tm.zero n, ⟨rfl, t₀, ht_close⟩,
                Or.inl ⟨n, rfl, rfl⟩⟩,
              ⟨hs.symm, s₀, hs.symm ▸ hs_close⟩⟩⟩
  · -- plus-succ: source `plus (succ x) y`, target `succ (plus x y)`.
    exact ⟨Tm.plus (Tm.succ x) y,
           Or.inl ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           ⟨Tm.succ (Tm.plus x y),
             ⟨Tm.plus (Tm.succ x) y, ⟨rfl, t₀, ht_close⟩,
               Or.inr (Or.inl ⟨x, y, rfl, rfl⟩)⟩,
             ⟨rfl, s₀, hs_close⟩⟩⟩
  · -- mult-zero: source `mult zero n`, target `zero` (via `hs : s = zero`).
    refine ⟨Tm.mult Tm.zero n,
            Or.inr ⟨Tm.zero, Tm.zero, n, n, rfl, rfl,
                    Or.inl ⟨rfl, rfl⟩, rfl⟩,
            ⟨Tm.zero,
              ⟨Tm.mult Tm.zero n, ⟨rfl, t₀, ht_close⟩,
                Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))⟩,
              ⟨hs.symm, s₀, hs.symm ▸ hs_close⟩⟩⟩
  · -- mult-succ: source `mult (succ x) y`, target `plus (mult x y) y`.
    exact ⟨Tm.mult (Tm.succ x) y,
           Or.inr ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           ⟨Tm.plus (Tm.mult x y) y,
             ⟨Tm.mult (Tm.succ x) y, ⟨rfl, t₀, ht_close⟩,
               Or.inr (Or.inr (Or.inr ⟨x, y, rfl, rfl⟩))⟩,
             ⟨rfl, s₀, hs_close⟩⟩⟩

/-- The closed part of the rule is deterministic: `(□r)ᵒ * □r ≤ 1`.
Immediate from `rule_isDeterministic` and the deflationarity `□a ≤ a`
on both sides. -/
theorem rule_boxed_isDeterministic :
    LeanTra.Algebra.IsDeterministic (SRA.box (rule : SynRel)) := by
  change ((SRA.box (rule : SynRel))ᵒ * SRA.box rule) ≤ 1
  calc (SRA.box (rule : SynRel))ᵒ * SRA.box rule
      ≤ (rule : SynRel)ᵒ * SRA.box rule :=
        mul_le_mul' (IsInvolutiveQuantale.converse_monotonicity (SRA.box_le _)) le_rfl
    _ ≤ (rule : SynRel)ᵒ * rule :=
        mul_le_mul' le_rfl (SRA.box_le _)
    _ ≤ 1 := rule_isDeterministic

/-- **Determinism of big-step Peano-arithmetic evaluation.** For the
closed part of the four-rule reduction system,
`(r^⇓)ᵒ * r^⇓ ≤ Δκ`. Direct instantiation of
`LeanTra.Determinism.bigStep_determinism` at `SRA.box rule`, with
the three hypotheses discharged just above. -/
theorem rule_bigStep_determinism :
    (LeanTra.Determinism.bigStepEvaluation (SRA.box (rule : SynRel)))ᵒ
        * LeanTra.Determinism.bigStepEvaluation (SRA.box rule)
      ≤ (OperationalDecomposition.valueCoreflexive : SynRel) :=
  LeanTra.Determinism.bigStep_determinism
    rule_boxed_gip
    (SRA.box_isClosed _)
    rule_boxed_isDeterministic

end SynRel

end LeanTra.Instances.PeanoArithmetic

/-!
A discipline the whole project follows: every non-trivial result is
followed by a `#print axioms` command. The list below runs through the
fifteen main results of the file. Each depends only on some combination
of `propext`, `Classical.choice`, and `Quot.sound` — the three standard
Lean 4 prelude axioms. No `sorryAx`, no opaque bridge assumption: the
instance is closed.
-/

#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.instIsInvolutiveQuantale
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.subst_varDiag_unit_right
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.scr_compositionality
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.subst_associativity
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.subst_compositionality_oplax
#print axioms LeanTra.Instances.PeanoArithmetic.instSRA
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.scr_decomposition
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.box_elimination_oplaxity
#print axioms LeanTra.Instances.PeanoArithmetic.instOperationalDecomposition
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_isReduction
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_isSubstitutiveAtIdentity
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_isDeterministic
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_gip
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_gcp
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_confluent
#print axioms LeanTra.Instances.PeanoArithmetic.SynRel.rule_bigStep_determinism
