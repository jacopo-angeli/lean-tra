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

/-!
# The Peano-fragment first-order term model of the SRA framework

The concrete non-trivial companion to the consistency model of
`Instances/Consistency.lean` and the λ-calculus instance of
`Instances/SecondOrder.lean`. We fix a two-symbol first-order signature
— `succ` (unary, introduction form) and `plus` (binary, elimination
form with slot `0` major, slot `1` minor) — build its term algebra
`Tm Γ` in an arbitrary type-valued context `Γ`, install on top of it
the involutive-quantale layer of `SynRel`, discharge the sixteen `SRA`
axioms and the four `j` axioms on the resulting carrier, and read off
confluence of the computation rule `plus(succ(x), y) → succ(plus(x, y))`
from the abstract bridge theorem `local_confluence`, whose two Gentzen
principles `GIP` and `GCP` are verified directly on the rule.

The file is organised in six sections. Section 1 fixes the syntax:
terms in context, substitution and renaming, and their equational
theory as a Kleisli category. Section 2 installs the relational carrier
`SynRel` together with the full involutive-quantale structure (lattice,
monoid, quantale, involution) built pointwise per context. Section 3
defines the four `SRA` operations (`varDiag`, `scr`, `subst`, `j`) and
discharges the nineteen accompanying axioms. Section 4 assembles the
SRA typeclass instance. Section 5 defines the constructor and
destructor relations `introduction` and `elimination`, discharges the
fourteen axioms of `OperationalDecomposition`, and assembles that
instance. Section 6 introduces the reduction rule, discharges the five
local hypotheses of the bridge theorem, and reads off confluence.

The main design decision, visible throughout, is that contexts are
*types* rather than finite subsets of a global variable universe: this
makes α-issues disappear at the syntax level and turns substitution
associativity into a dependent-sum merge, at the cost of promoting
every context to a genuinely different type.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System
  Metatheory.* LICS 2026, Example 18 (adapted: `succ` in place of a
  nullary constant, so both introduction and elimination forms fit the
  arity conventions of the algebraic framework).
-/
@[expose] public section

set_option linter.style.show false
set_option linter.unusedTactic false

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.FirstOrder

/-! ## Section 1: Terms

The syntax: two constructors `succ` (unary) and `plus` (binary), on top
of variables drawn from a context type `Γ`. Substitution and renaming
are defined by direct recursion, and their equational theory reads as
the identity and associativity of a Kleisli category via the auxiliary
`Subst.id` / `Subst.comp`.

Contexts are *types*, not finite subsets of a global variable universe.
Under this reading, renamings `Γ → Δ` and substitutions `Γ → Tm Δ` are
plain functions, and closed terms are `Tm Empty`. Finiteness of
contexts is not used anywhere in the SRA axioms; the price is that a
term and any of its weakenings are distinct objects that must be
transported by an explicit `Tm.ren`. -/

/-- The terms of the Peano fragment: a variable, a successor node, or a
plus node. -/
inductive Tm (Γ : Type) where
  /-- A variable term. -/
  | var  : Γ → Tm Γ
  /-- Unary successor: `succ(x)`. -/
  | succ : Tm Γ → Tm Γ
  /-- Binary plus: `plus(m, n)`, with `m` the eagerly-evaluated major
  argument. -/
  | plus : Tm Γ → Tm Γ → Tm Γ

namespace Tm

variable {Γ Δ E : Type}

/-- Simultaneous capture-free substitution: `t.subst τ` replaces every
variable `x : Γ` in `t` by `τ x : Tm Δ`. Since contexts are types and
variables have no binding structure, there is no capture to avoid. -/
def subst : Tm Γ → (Γ → Tm Δ) → Tm Δ
  | var x,     τ => τ x
  | succ t,    τ => succ (t.subst τ)
  | plus m n,  τ => plus (m.subst τ) (n.subst τ)

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

/-! ### Reduction laws on constructors -/

@[simp] theorem subst_var (x : Γ) (τ : Γ → Tm Δ) : (var x).subst τ = τ x := rfl

@[simp] theorem subst_succ (t : Tm Γ) (τ : Γ → Tm Δ) :
    (succ t).subst τ = succ (t.subst τ) := rfl

@[simp] theorem subst_plus (m n : Tm Γ) (τ : Γ → Tm Δ) :
    (plus m n).subst τ = plus (m.subst τ) (n.subst τ) := rfl

@[simp] theorem ren_var (x : Γ) (f : Γ → Δ) : (var x : Tm Γ).ren f = var (f x) := rfl

@[simp] theorem ren_succ (t : Tm Γ) (f : Γ → Δ) :
    (succ t).ren f = succ (t.ren f) := rfl

@[simp] theorem ren_plus (m n : Tm Γ) (f : Γ → Δ) :
    (plus m n).ren f = plus (m.ren f) (n.ren f) := rfl

/-! ### Structural inductions -/

/-- The identity substitution is a right identity for `subst`. -/
theorem subst_id (t : Tm Γ) : t.subst Subst.id = t := by
  induction t with
  | var x    => rfl
  | succ t ih => simp [Tm.subst, ih]
  | plus m n ihm ihn => simp [Tm.subst, ihm, ihn]

/-- Substitution respects Kleisli composition. -/
theorem subst_comp (t : Tm Γ) (τ : Γ → Tm Δ) (θ : Δ → Tm E) :
    (t.subst τ).subst θ = t.subst (Subst.comp τ θ) := by
  induction t with
  | var x    => rfl
  | succ t ih => simp [Tm.subst, ih]
  | plus m n ihm ihn => simp [Tm.subst, ihm, ihn]

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
  | succ t ih => simp [Tm.subst, ih]
  | plus m n ihm ihn => simp [Tm.subst, ihm, ihn]

/-- Injectivity of renaming. -/
theorem ren_injective (f : Γ → Δ) (hf : Function.Injective f) :
    Function.Injective (fun t : Tm Γ => t.ren f) := by
  intro t
  induction t with
  | var x =>
    intro s h
    cases s with
    | var y   => exact congrArg Tm.var (hf (Tm.var.inj h))
    | succ _  => cases h
    | plus _ _ => cases h
  | succ t ih =>
    intro s h
    cases s with
    | var _    => cases h
    | succ s'  => exact congrArg Tm.succ (ih (Tm.succ.inj h))
    | plus _ _ => cases h
  | plus m n ihm ihn =>
    intro s h
    cases s with
    | var _    => cases h
    | succ _   => cases h
    | plus m' n' =>
      obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp h
      exact congrArg₂ Tm.plus (ihm hm) (ihn hn)

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

/-! ### Closed terms and their weakening

`ClosedTm := Tm Empty`: terms with no free variables. Every closed term
embeds into an arbitrary context via the unique `Empty → Γ`, and
substitution acts trivially on the image of this embedding. -/

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

/-! ## Section 2: Renaming-closed context-indexed relations

A `SynRel` is a family of binary relations on `Tm Γ`, one per context
type `Γ`, uniformly closed under renaming. The full involutive-quantale
structure is inherited pointwise from `Prop`. -/

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

/-! ### Order and pointwise lattice operations -/

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

/-! ### `.rel` accessors -/

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

/-! ### Complete lattice -/

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

/-! ### Composition, identity, quantale, involution -/

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

/-! ### Non-degeneracy -/

theorem bot_ne_top : (⊥ : SynRel) ≠ ⊤ := by
  intro h
  have hle : (⊤ : SynRel) ≤ ⊥ := h ▸ le_refl _
  exact hle Unit (Tm.var ()) (Tm.var ()) trivial

instance instNontrivial : Nontrivial SynRel := ⟨⊥, ⊤, bot_ne_top⟩

/-! ## Section 3: SRA operations and their axioms

Four operations: `varDiag` (diagonal on variables), `scr` (strict
compatible refinement: same head, args pairwise related), `subst`
(relation substitution), `j` (identity restricted to weakened closed
terms). The nineteen accompanying axioms are proved in three groups by
ascending difficulty. -/

/-- The variable co-equivalence: two terms are related when they are
the same variable. -/
def varDiag : SynRel := {
  rel := fun Γ t s => ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩
}

/-- Strict compatible refinement: two terms are related when they are
built with the same outermost constructor whose immediate sub-terms
are pairwise `φ`-related. -/
def scr (φ : SynRel) : SynRel := {
  rel := fun Γ t s =>
    (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ φ.rel Γ t' s') ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                            φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂)
  ren_closed := by
    intro Γ Δ f t s h
    rcases h with ⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
    · exact Or.inl ⟨t'.ren f, s'.ren f, rfl, rfl, φ.ren_closed f hφ⟩
    · exact Or.inr ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f, rfl, rfl,
                    φ.ren_closed f hφm, φ.ren_closed f hφn⟩
}

/-- Relation substitution: `subst φ ψ` (`φ[ψ]`) at context `Θ` relates
two terms `u v : Tm Θ` when there exist a source context `Γ` with
pre-substitution terms `t s : Tm Γ` and substitutions `τ σ : Γ → Tm Θ`
such that `u = t.subst τ`, `v = s.subst σ`, `t` and `s` are `φ`-related
in `Γ`, and `τ x`, `σ x` are pointwise `ψ`-related in `Θ`. -/
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

/-! ### `.rel` accessors -/

@[simp] theorem varDiag_rel {Γ} {t s : Tm Γ} :
    (varDiag : SynRel).rel Γ t s ↔ ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x :=
  Iff.rfl

@[simp] theorem scr_rel {φ : SynRel} {Γ} {t s : Tm Γ} :
    (scr φ).rel Γ t s ↔
      (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ φ.rel Γ t' s') ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                              φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) := Iff.rfl

@[simp] theorem subst_rel {φ ψ : SynRel} {Θ} {u v : Tm Θ} :
    (subst φ ψ).rel Θ u v ↔
      ∃ (Γ : Type) (t s : Tm Γ) (τ σ : Γ → Tm Θ),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel Γ t s ∧ ∀ x, ψ.rel Θ (τ x) (σ x) := Iff.rfl

/-! ### Group 1: the easy axioms -/

theorem scr_monotonicity {φ ψ : SynRel} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro Γ t s hs
  rcases hs with ⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · exact Or.inl ⟨t', s', rfl, rfl, h Γ t' s' hφ⟩
  · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                  h Γ m₁ m₂ hφm, h Γ n₁ n₂ hφn⟩

theorem subst_monotonicity_right {φ ψ ψ' : SynRel} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro Θ u v hs
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨Γ, t, s, τ, σ, hu, hv, hφ, fun x => h Θ (τ x) (σ x) (hψ x)⟩

theorem scr_converse_commutation (φ : SynRel) : scr (φᵒ) = (scr φ)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩

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
  rcases hscr with ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ <;> cases hu

/-! ### Group 2: the medium axioms -/

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
  rcases hscr with ⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · refine Or.inl ⟨t'.subst τ, s'.subst σ, by rw [hu]; rfl, by rw [hv]; rfl, ?_⟩
    exact ⟨Γ, t', s', τ, σ, rfl, rfl, hφ, hψ⟩
  · refine Or.inr ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
                   by rw [hu]; rfl, by rw [hv]; rfl, ?_, ?_⟩
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, hφm, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hφn, hψ⟩

theorem scr_compositionality (φ ψ : SynRel) : scr (φ * ψ) = scr φ * scr ψ := by
  ext Γ t v
  constructor
  · rintro (⟨t', v', rfl, rfl, ⟨u, hφ, hψ⟩⟩ |
            ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨u_m, hφm, hψm⟩, ⟨u_n, hφn, hψn⟩⟩)
    · refine ⟨Tm.succ u, Or.inl ⟨t', u, rfl, rfl, hφ⟩, Or.inl ⟨u, v', rfl, rfl, hψ⟩⟩
    · refine ⟨Tm.plus u_m u_n,
              Or.inr ⟨m₁, u_m, n₁, u_n, rfl, rfl, hφm, hφn⟩,
              Or.inr ⟨u_m, m₂, u_n, n₂, rfl, rfl, hψm, hψn⟩⟩
  · rintro ⟨w, h1, h2⟩
    rcases h1 with ⟨t', w', rfl, rfl, hφ⟩ | ⟨m₁, wm, n₁, wn, rfl, rfl, hφm, hφn⟩
    · rcases h2 with ⟨w'', v', hw, rfl, hψ⟩ | ⟨_, _, _, _, hw, _, _, _⟩
      · have : w' = w'' := Tm.succ.inj hw
        subst this
        exact Or.inl ⟨t', v', rfl, rfl, ⟨w', hφ, hψ⟩⟩
      · cases hw
    · rcases h2 with ⟨_, _, hw, _⟩ | ⟨wm', m₂, wn', n₂, hw, rfl, hψm, hψn⟩
      · cases hw
      · obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp hw
        subst hm; subst hn
        exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, hφm, hψm⟩, ⟨wn, hφn, hψn⟩⟩

theorem cr_fixpoint : (varDiag ⊔ scr 1 : SynRel) = 1 := by
  ext Γ t s
  constructor
  · intro h
    rcases h with ⟨x, rfl, rfl⟩ | (⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · rfl
    · exact congrArg Tm.succ hφ
    · exact congrArg₂ Tm.plus hφm hφn
  · intro (h : t = s)
    subst h
    cases t with
    | var x => exact Or.inl ⟨x, rfl, rfl⟩
    | succ t' => exact Or.inr (Or.inl ⟨t', t', rfl, rfl, rfl⟩)
    | plus m n => exact Or.inr (Or.inr ⟨m, m, n, n, rfl, rfl, rfl, rfl⟩)

theorem cr_induction {φ : SynRel}
    (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
  intro Γ t s (heq : t = s)
  subst heq
  induction t with
  | var x =>
    exact h Γ (Tm.var x) (Tm.var x) (Or.inl ⟨x, rfl, rfl⟩)
  | succ t' ih =>
    exact h Γ (Tm.succ t') (Tm.succ t')
      (Or.inr (Or.inl ⟨t', t', rfl, rfl, ih⟩))
  | plus m n ihm ihn =>
    exact h Γ (Tm.plus m n) (Tm.plus m n)
      (Or.inr (Or.inr ⟨m, m, n, n, rfl, rfl, ihm, ihn⟩))

/-! ### Group 3: the hard axioms -/

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

/-! ### The closure constant `j` and its axioms -/

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
  | succ _  => cases hcls
  | plus _ _ => cases hcls

end SynRel

/-! ## Section 4: The `SRA` instance and non-degeneracy -/

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
    Or.inl ⟨Tm.var (), Tm.var (), rfl, rfl, trivial⟩
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

/-! ## Section 5: Operational decomposition

The constructor and destructor parts of the strict compatible
refinement: `introduction φ` relates two `succ`-nodes with pairwise
`φ`-related bodies; `elimination φ ψ` relates two `plus`-nodes with
major-slot `φ`-related and minor-slot `ψ`-related. -/

namespace SynRel

/-- Introduction forms: `(succ t', succ s')` with `φ`-related bodies. -/
def introduction (a : SynRel) : SynRel := {
  rel := fun Γ t s => ∃ t' s' : Tm Γ,
    t = Tm.succ t' ∧ s = Tm.succ s' ∧ a.rel Γ t' s'
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨t', s', ht, hs, ha⟩ := h
    exact ⟨t'.ren f, s'.ren f, by rw [ht]; rfl, by rw [hs]; rfl,
           a.ren_closed f ha⟩
}

/-- Elimination forms: `(plus m₁ n₁, plus m₂ n₂)` with major `a`-related
and minor `b`-related. -/
def elimination (a b : SynRel) : SynRel := {
  rel := fun Γ t s => ∃ m₁ m₂ n₁ n₂ : Tm Γ,
    t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
    a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨m₁, m₂, n₁, n₂, ht, hs, ha, hb⟩ := h
    exact ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
           by rw [ht]; rfl, by rw [hs]; rfl,
           a.ren_closed f ha, b.ren_closed f hb⟩
}

@[simp] theorem introduction_rel {a : SynRel} {Γ} {t s : Tm Γ} :
    (introduction a).rel Γ t s ↔
      ∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ a.rel Γ t' s' :=
  Iff.rfl

@[simp] theorem elimination_rel {a b : SynRel} {Γ} {t s : Tm Γ} :
    (elimination a b).rel Γ t s ↔
      ∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
        a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂ := Iff.rfl

/-! ### Join preservation, compositionality, converse -/

theorem introduction_join_preservation (𝒮 : Set SynRel) :
    introduction (sSup 𝒮) = sSup (introduction '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩
    exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
    exact ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩

theorem introduction_compositionality (a b : SynRel) :
    introduction (a * b) = introduction a * introduction b := by
  ext Γ t v
  constructor
  · rintro ⟨t', v', rfl, rfl, u', ha, hb⟩
    exact ⟨Tm.succ u',
           ⟨t', u', rfl, rfl, ha⟩,
           ⟨u', v', rfl, rfl, hb⟩⟩
  · rintro ⟨u, ⟨t', u₁, rfl, hu, ha⟩, ⟨u₂, v', hu', rfl, hb⟩⟩
    have hu12 : u₁ = u₂ := Tm.succ.inj (hu.symm.trans hu')
    refine ⟨t', v', rfl, rfl, u₁, ha, ?_⟩
    rw [hu12]; exact hb

theorem introduction_converse_commutation (a : SynRel) :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext Γ t s
  constructor
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩

theorem elimination_join_preservation_left (𝒮 : Set SynRel) (b : SynRel) :
    elimination (sSup 𝒮) b = sSup ((fun a => elimination a b) '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
    exact ⟨elimination φ b, ⟨φ, hφ𝒮, rfl⟩,
           m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩
    exact ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩

theorem elimination_join_preservation_right (a : SynRel) (𝒮 : Set SynRel) :
    elimination a (sSup 𝒮) = sSup ((fun b => elimination a b) '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩
    exact ⟨elimination a φ, ⟨φ, hφ𝒮, rfl⟩,
           m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩
    exact ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩

theorem elimination_compositionality (a₁ a₂ b₁ b₂ : SynRel) :
    elimination (a₁ * a₂) (b₁ * b₂) = elimination a₁ b₁ * elimination a₂ b₂ := by
  ext Γ t v
  constructor
  · rintro ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, ha₁, ha₂⟩, ⟨wn, hb₁, hb₂⟩⟩
    exact ⟨Tm.plus wm wn,
           ⟨m₁, wm, n₁, wn, rfl, rfl, ha₁, hb₁⟩,
           ⟨wm, m₂, wn, n₂, rfl, rfl, ha₂, hb₂⟩⟩
  · rintro ⟨u, ⟨m₁, um, n₁, un, rfl, hu, ha₁, hb₁⟩,
             ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩⟩
    have heq : Tm.plus um un = Tm.plus um' un' := hu.symm.trans hu'
    obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
    subst hm; subst hn
    exact ⟨m₁, m₂, n₁, n₂, rfl, rfl,
           ⟨um, ha₁, ha₂⟩, ⟨un, hb₁, hb₂⟩⟩

theorem elimination_converse_commutation (a b : SynRel) :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext Γ t s
  constructor
  · rintro ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
    exact ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
  · rintro ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
    exact ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩

/-! ### Unit oplaxity, orthogonality, and the decomposition -/

theorem introduction_unit_oplaxity : (introduction 1 : SynRel) ≤ 1 := by
  rintro Γ t s ⟨t', s', rfl, rfl, (heq : t' = s')⟩
  exact congrArg Tm.succ heq

theorem elimination_unit_oplaxity : (elimination 1 1 : SynRel) ≤ 1 := by
  rintro Γ t s ⟨m₁, m₂, n₁, n₂, rfl, rfl, (hm : m₁ = m₂), (hn : n₁ = n₂)⟩
  exact congrArg₂ Tm.plus hm hn

theorem introduction_elimination_orthogonality (a b c : SynRel) :
    introduction a * elimination b c ≤ ⊥ := by
  rintro Γ t v ⟨u, ⟨t', u', rfl, hu, _⟩, ⟨_, _, _, _, hu', _, _, _⟩⟩
  exact absurd (hu.symm.trans hu') (by intro h; cases h)

theorem scr_decomposition (a : SynRel) :
    (SRA.scr a : SynRel) = introduction a ⊔ elimination a a := by
  ext Γ t s
  constructor
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨t', s', rfl, rfl, hφ⟩
    · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨t', s', rfl, rfl, hφ⟩
    · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩

/-! ### Substitution and closure oplaxities -/

theorem subst_introduction_oplaxity (a b : SynRel) :
    subst (introduction a) b ≤ introduction (subst a b) := by
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨t', s', rfl, rfl, ha⟩, hψ⟩
  refine ⟨t'.subst τ, s'.subst σ, rfl, rfl, ?_⟩
  exact ⟨Γ, t', s', τ, σ, rfl, rfl, ha, hψ⟩

theorem subst_elimination_oplaxity (a b c : SynRel) :
    subst (elimination a b) c ≤ elimination (subst a c) (subst b c) := by
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl,
                ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩, hψ⟩
  refine ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ, rfl, rfl, ?_, ?_⟩
  · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, ha, hψ⟩
  · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hb, hψ⟩

theorem box_elimination_oplaxity (a b : SynRel) :
    (SRA.box (elimination a b) : SynRel) ≤ elimination (SRA.box a) b := by
  intro Θ u v h
  obtain ⟨w, hjeab, hjwv⟩ := h
  obtain ⟨w', hju, hab⟩ := hjeab
  obtain ⟨huw', u₀, hu_close⟩ := hju
  subst huw'
  obtain ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, hab_maj, hab_min⟩ := hab
  obtain ⟨hwv, v₀, hv_close⟩ := hjwv
  subst hwv
  -- u₀ : ClosedTm; close Θ u₀ = plus m₁ n₁
  cases u₀ with
  | var x => exact x.elim
  | succ _ =>
    have : Tm.close Θ (Tm.succ _) = Tm.plus m₁ n₁ := hu_close.symm.trans hu_eq
    cases this
  | plus u₀m u₀n =>
    have hu_shape :
        Tm.plus (Tm.close Θ u₀m) (Tm.close Θ u₀n) = Tm.plus m₁ n₁ :=
      hu_close.symm.trans hu_eq
    obtain ⟨hm_eq, hn_eq⟩ := Tm.plus.injEq _ _ _ _ |>.mp hu_shape
    cases v₀ with
    | var x => exact x.elim
    | succ _ =>
      have : Tm.close Θ (Tm.succ _) = Tm.plus m₂ n₂ := hv_close.symm.trans hw_eq
      cases this
    | plus v₀m v₀n =>
      have hv_shape :
          Tm.plus (Tm.close Θ v₀m) (Tm.close Θ v₀n) = Tm.plus m₂ n₂ :=
        hv_close.symm.trans hw_eq
      obtain ⟨hm_eq', hn_eq'⟩ := Tm.plus.injEq _ _ _ _ |>.mp hv_shape
      refine ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, ?_, hab_min⟩
      refine ⟨m₂, ⟨m₁, ⟨rfl, u₀m, hm_eq.symm⟩, hab_maj⟩,
              ⟨rfl, v₀m, hm_eq'.symm⟩⟩

end SynRel

/-! ### The `OperationalDecomposition` instance -/

instance instOperationalDecomposition : OperationalDecomposition SynRel where
  introduction := SynRel.introduction
  elimination := SynRel.elimination
  introduction_join_preservation := SynRel.introduction_join_preservation
  introduction_compositionality := SynRel.introduction_compositionality
  introduction_converse_commutation := SynRel.introduction_converse_commutation
  elimination_join_preservation_left := SynRel.elimination_join_preservation_left
  elimination_join_preservation_right := SynRel.elimination_join_preservation_right
  elimination_compositionality := SynRel.elimination_compositionality
  elimination_converse_commutation := SynRel.elimination_converse_commutation
  introduction_unit_oplaxity := SynRel.introduction_unit_oplaxity
  elimination_unit_oplaxity := SynRel.elimination_unit_oplaxity
  introduction_elimination_orthogonality := SynRel.introduction_elimination_orthogonality
  scr_decomposition := SynRel.scr_decomposition
  subst_introduction_oplaxity := SynRel.subst_introduction_oplaxity
  subst_elimination_oplaxity := SynRel.subst_elimination_oplaxity
  box_elimination_oplaxity := SynRel.box_elimination_oplaxity

/-! ## Section 6: The Peano-fragment reduction rule and confluence

The computation rule `plus(succ(x), y) ↦ succ(plus(x, y))` — the
successor propagates out of a plus — packaged as a `SynRel`, together
with the five local hypotheses of the bridge theorem and the
confluence corollary via `LeanTra.Confluence.local_confluence`. -/

namespace SynRel

/-- The Peano-fragment reduction rule. -/
def rule : SynRel := {
  rel := fun Γ t s =>
    ∃ (x y : Tm Γ), t = Tm.plus (Tm.succ x) y ∧ s = Tm.succ (Tm.plus x y)
  ren_closed := by
    intro Γ Δ f t s h
    obtain ⟨x, y, rfl, rfl⟩ := h
    exact ⟨x.ren f, y.ren f, by simp, by simp⟩
}

@[simp] theorem rule_rel {Γ} {t s : Tm Γ} :
    (rule : SynRel).rel Γ t s ↔
      ∃ (x y : Tm Γ), t = Tm.plus (Tm.succ x) y ∧ s = Tm.succ (Tm.plus x y) :=
  Iff.rfl

theorem rule_isReduction : LeanTra.Confluence.IsReduction (rule : SynRel) := by
  change (SRA.varDiag * rule : SynRel) = ⊥
  ext Γ t v
  constructor
  · rintro ⟨m, ⟨z, rfl, rfl⟩, x, y, hm, _⟩
    cases hm
  · intro h; exact h.elim

theorem rule_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (rule : SynRel) := by
  change (SRA.subst rule 1 : SynRel) ≤ rule
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨x, y, rfl, rfl⟩, hτσ⟩
  have hτσ_eq : τ = σ := funext hτσ
  subst hτσ_eq
  exact ⟨x.subst τ, y.subst τ, by simp, by simp⟩

theorem rule_isDeterministic : LeanTra.Confluence.IsDeterministic (rule : SynRel) := by
  change ((rule : SynRel)ᵒ * rule) ≤ 1
  rintro Γ t t' ⟨m, ⟨x, y, hm, rfl⟩, x', y', hm', rfl⟩
  have heq : Tm.plus (Tm.succ x) y = Tm.plus (Tm.succ x') y' :=
    hm.symm.trans hm'
  obtain ⟨hs, rfl⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
  have hx : x = x' := Tm.succ.inj hs
  subst hx
  rfl

theorem rule_gip : LeanTra.Metatheory.GIP (rule : SynRel) := by
  intro Γ t s hrule
  obtain ⟨x, y, rfl, rfl⟩ := hrule
  refine ⟨Tm.plus (Tm.succ x) y,
          ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl, ?_, rfl⟩,
          x, y, rfl, rfl⟩
  exact ⟨x, x, rfl, rfl, rfl⟩

theorem rule_gcp : LeanTra.Metatheory.GCP (rule : SynRel) := by
  intro rx hcompat
  change (OperationalDecomposition.elimination (SRA.cr rx) rx : SynRel)
           * (rule : SynRel)
       ≤ (rule : SynRel) * SRA.subst rx rx
  rintro Γ t v ⟨m, helim, x', y', hm, rfl⟩
  subst hm
  obtain ⟨m₁, m₂, n₁, n₂, ht_eq, hm_eq, hmaj, hmin⟩ := helim
  -- hm_eq : plus (succ x') y' = plus m₂ n₂
  obtain ⟨hm2_eq, hn2_eq⟩ := Tm.plus.injEq _ _ _ _ |>.mp hm_eq
  subst hm2_eq; subst hn2_eq
  -- Now hmaj : cr rx (m₁, succ x'), hmin : rx (n₁, y'), t = plus m₁ n₁
  -- Case-split on cr rx = varDiag ⊔ scr rx
  unfold SRA.cr at hmaj
  rcases hmaj with ⟨z, _, hvar⟩ | hscr
  · cases hvar  -- succ x' can't be a variable
  · rcases hscr with ⟨u, u', hm1_eq, hux, hrx⟩ | ⟨_, _, _, _, _, hux', _, _⟩
    · -- succ case: m₁ = succ u, succ x' = succ u', rx u u'
      subst hm1_eq
      have hxu' : x' = u' := Tm.succ.inj hux
      subst hxu'
      refine ⟨Tm.succ (Tm.plus u n₁), ⟨u, n₁, ht_eq, rfl⟩, ?_⟩
      -- Build subst(rx, rx)(succ (plus u n₁), succ (plus x' y'))
      -- Source context: Bool, with `false ↦ major slot`, `true ↦ minor slot`.
      refine ⟨Bool,
              Tm.succ (Tm.plus (Tm.var false) (Tm.var true)),
              Tm.succ (Tm.plus (Tm.var false) (Tm.var true)),
              fun b : Bool => if b then n₁ else u,
              fun b : Bool => if b then y' else x',
              rfl, rfl, ?_, ?_⟩
      · -- rx-reflexivity on succ (plus (var false) (var true))
        have hvar_refl : ∀ (b : Bool), rx.rel Bool (Tm.var b) (Tm.var b) :=
          fun b => hcompat _ _ _ (Or.inl ⟨b, rfl, rfl⟩)
        have h_scr_plus :
            (SRA.scr rx : SynRel).rel Bool
              (Tm.plus (Tm.var false) (Tm.var true))
              (Tm.plus (Tm.var false) (Tm.var true)) :=
          Or.inr ⟨_, _, _, _, rfl, rfl, hvar_refl _, hvar_refl _⟩
        have h_rx_plus :
            rx.rel Bool
              (Tm.plus (Tm.var false) (Tm.var true))
              (Tm.plus (Tm.var false) (Tm.var true)) :=
          hcompat _ _ _ (Or.inr h_scr_plus)
        have h_scr_succ :
            (SRA.scr rx : SynRel).rel Bool
              (Tm.succ (Tm.plus (Tm.var false) (Tm.var true)))
              (Tm.succ (Tm.plus (Tm.var false) (Tm.var true))) :=
          Or.inl ⟨_, _, rfl, rfl, h_rx_plus⟩
        exact hcompat _ _ _ (Or.inr h_scr_succ)
      · intro b
        cases b <;> simp [*, hrx, hmin]
    · -- plus case: succ x' can't be a plus node
      cases hux'

/-- Confluence of parallel reduction on the Peano-fragment rule,
concluded from the Gentzen inversion and conservation principles via
the abstract bridge theorem. -/
theorem rule_confluent :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (rule : SynRel)) :=
  LeanTra.Confluence.local_confluence
    rule_isReduction
    rule_isSubstitutiveAtIdentity
    rule_isDeterministic
    rule_gip
    rule_gcp

end SynRel

end LeanTra.Instances.FirstOrder

/-! ## Axiom trace

Explicit `#print axioms` commands on the main results. Every downstream
theorem depends on `propext`, `Classical.choice`, and `Quot.sound` (the
three standard Lean-prelude axioms); no non-standard assumption is
required. -/

#print axioms LeanTra.Instances.FirstOrder.SynRel.instIsInvolutiveQuantale
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_varDiag_unit_right
#print axioms LeanTra.Instances.FirstOrder.SynRel.scr_compositionality
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_associativity
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_compositionality_oplax
#print axioms LeanTra.Instances.FirstOrder.instSRA
#print axioms LeanTra.Instances.FirstOrder.SynRel.scr_decomposition
#print axioms LeanTra.Instances.FirstOrder.SynRel.box_elimination_oplaxity
#print axioms LeanTra.Instances.FirstOrder.instOperationalDecomposition
#print axioms LeanTra.Instances.FirstOrder.SynRel.rule_isReduction
#print axioms LeanTra.Instances.FirstOrder.SynRel.rule_isSubstitutiveAtIdentity
#print axioms LeanTra.Instances.FirstOrder.SynRel.rule_isDeterministic
#print axioms LeanTra.Instances.FirstOrder.SynRel.rule_gip
#print axioms LeanTra.Instances.FirstOrder.SynRel.rule_gcp
#print axioms LeanTra.Instances.FirstOrder.SynRel.rule_confluent
