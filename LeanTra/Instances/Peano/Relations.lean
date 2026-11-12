/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Syntax.Arith
public import LeanTra.ToMathlib.Algebra.Order.Quantale.Involutive

/-!
# Relations on Peano terms

Renaming-closed, context-indexed relations on `Tm` form an involutive quantale.

## Main definitions
* `TrmRel`: context-indexed families of binary relations on `Tm Γ`, closed under renaming.
* `TrmRel.converse`: the involution swapping the two endpoints of a relation.

## Main statements
* `TrmRel.instCompleteLattice`: pointwise complete lattice on `TrmRel`.
* `TrmRel.instMonoid`, `TrmRel.instIsQuantale`: relational composition as a quantale structure.
* `TrmRel.instIsInvolutiveQuantale`: converse upgrades the quantale to an involutive quantale.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.* LICS 2026
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.PeanoArithmetic

/-!
With the syntactic layer in place, we now construct the algebraic
carrier on which the whole TRA machinery will live: `TrmRel`, the type
of renaming-closed context-indexed binary relations on `Tm`. Concretely
an element of `TrmRel` is a family of binary relations `φ.rel Γ : Tm Γ
→ Tm Γ → Prop`, one per context type Γ, together with a coherence
condition — the family is closed under renaming. The coherence
condition is the minimal amount of syntax-sensitivity the definition
needs; every operation defined on top of `TrmRel` will preserve it, so
we never have to think about it explicitly again.

Pointwise from `Prop`, `TrmRel` inherits a complete lattice (order is
pointwise implication, meets and joins are conjunction and disjunction),
a monoid whose product is relational composition `∃ u, φ t u ∧ ψ u v`
and whose unit is the pointwise identity `t = s`, a quantale
(composition distributes over arbitrary joins), and an involution
(converse swaps the two arguments). These four layers of structure are
exactly the algebraic content the `TRA` typeclass expects of its
carrier, so once `TrmRel` carries them, the class hypotheses of every
downstream lemma will be discharged automatically.
-/

/-- A *syntax relation*: a family of binary relations on `Tm Γ`, one
per context type `Γ`, closed under renaming. -/
structure TrmRel : Type 1 where
  rel : (Γ : Type) → Tm Γ → Tm Γ → Prop
  ren_closed : ∀ {Γ Δ : Type} (f : Γ → Δ) {t s : Tm Γ},
                 rel Γ t s → rel Δ (t.ren f) (s.ren f)

namespace TrmRel

@[ext]
theorem ext {φ ψ : TrmRel}
    (h : ∀ Γ (t s : Tm Γ), φ.rel Γ t s ↔ ψ.rel Γ t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ
  obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by funext Γ t s; exact propext (h Γ t s)
  subst hrel; rfl

/-!
The order on `TrmRel` is pointwise implication, `⊤` and `⊥` are the
constantly-true and constantly-false families, meets and joins are
pointwise conjunction and disjunction, and arbitrary sups and infs
follow the same pattern using an existential (resp. universal) over
the index set. Each of these operations preserves renaming-closure by
inspection.
-/

instance instLE : LE TrmRel :=
  ⟨fun φ ψ => ∀ Γ (t s : Tm Γ), φ.rel Γ t s → ψ.rel Γ t s⟩

theorem le_iff {φ ψ : TrmRel} :
    φ ≤ ψ ↔ ∀ Γ (t s : Tm Γ), φ.rel Γ t s → ψ.rel Γ t s := Iff.rfl

instance instTop : Top TrmRel := ⟨{
  rel := fun _ _ _ => True
  ren_closed := by intros; trivial
}⟩

instance instBot : Bot TrmRel := ⟨{
  rel := fun _ _ _ => False
  ren_closed := by intros _ _ _ _ _ h; exact h.elim
}⟩

instance instMax : Max TrmRel := ⟨fun φ ψ => {
  rel := fun Γ t s => φ.rel Γ t s ∨ ψ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    exact h.imp (φ.ren_closed f) (ψ.ren_closed f)
}⟩

instance instMin : Min TrmRel := ⟨fun φ ψ => {
  rel := fun Γ t s => φ.rel Γ t s ∧ ψ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    exact ⟨φ.ren_closed f h.1, ψ.ren_closed f h.2⟩
}⟩

instance instSupSet : SupSet TrmRel := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∃ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩
}⟩

instance instInfSet : InfSet TrmRel := ⟨fun 𝒮 => {
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
    (⊤ : TrmRel).rel Γ t s ↔ True := Iff.rfl

@[simp] theorem bot_rel {Γ} {t s : Tm Γ} :
    (⊥ : TrmRel).rel Γ t s ↔ False := Iff.rfl

@[simp] theorem sup_rel {φ ψ : TrmRel} {Γ} {t s : Tm Γ} :
    (φ ⊔ ψ).rel Γ t s ↔ φ.rel Γ t s ∨ ψ.rel Γ t s := Iff.rfl

@[simp] theorem inf_rel {φ ψ : TrmRel} {Γ} {t s : Tm Γ} :
    (φ ⊓ ψ).rel Γ t s ↔ φ.rel Γ t s ∧ ψ.rel Γ t s := Iff.rfl

@[simp] theorem sSup_rel {𝒮 : Set TrmRel} {Γ} {t s : Tm Γ} :
    (sSup 𝒮).rel Γ t s ↔ ∃ φ ∈ 𝒮, φ.rel Γ t s := Iff.rfl

@[simp] theorem sInf_rel {𝒮 : Set TrmRel} {Γ} {t s : Tm Γ} :
    (sInf 𝒮).rel Γ t s ↔ ∀ φ ∈ 𝒮, φ.rel Γ t s := Iff.rfl

theorem iSup_rel {κ : Sort*} {f : κ → TrmRel} {Γ} {t s : Tm Γ} :
    (⨆ i, f i).rel Γ t s ↔ ∃ i, (f i).rel Γ t s := by
  rw [iSup, sSup_rel]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

theorem biSup_rel {α : Type*} {s : Set α} {f : α → TrmRel}
    {Γ} {t st : Tm Γ} :
    (⨆ a ∈ s, f a).rel Γ t st ↔ ∃ a ∈ s, (f a).rel Γ t st := by
  simp only [iSup_rel]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, h⟩

/-!
Assembly of the pointwise operations into a `CompleteLattice TrmRel`
instance. Each field is discharged by the corresponding pointwise fact
already proved.
-/

instance instCompleteLattice : CompleteLattice TrmRel where
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
`sSup`, and converse: together these promote `TrmRel` from a complete
lattice to an involutive quantale, exactly the algebraic layer the TRA
typeclass takes for granted.
-/

instance instMul : Mul TrmRel := ⟨fun φ ψ => {
  rel := fun Γ t v => ∃ u, φ.rel Γ t u ∧ ψ.rel Γ u v
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨u.ren f, φ.ren_closed f htu, ψ.ren_closed f huv⟩
}⟩

instance instOne : One TrmRel := ⟨{
  rel := fun _ t s => t = s
  ren_closed := by
    intros _ _ f _ _ h; exact congrArg (Tm.ren · f) h
}⟩

@[simp] theorem mul_rel {φ ψ : TrmRel} {Γ} {t v : Tm Γ} :
    (φ * ψ).rel Γ t v ↔ ∃ u, φ.rel Γ t u ∧ ψ.rel Γ u v := Iff.rfl

@[simp] theorem one_rel {Γ} {t s : Tm Γ} :
    (1 : TrmRel).rel Γ t s ↔ t = s := Iff.rfl

instance instMonoid : Monoid TrmRel where
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

instance instIsQuantale : IsQuantale TrmRel where
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

def converse (φ : TrmRel) : TrmRel := {
  rel := fun Γ t s => φ.rel Γ s t
  ren_closed := by
    intros _ _ f _ _ h; exact φ.ren_closed f h
}

@[simp] theorem converse_rel (φ : TrmRel) {Γ} {t s : Tm Γ} :
    (converse φ).rel Γ t s ↔ φ.rel Γ s t := Iff.rfl

instance instIsInvolutiveQuantale : IsInvolutiveQuantale TrmRel where
  converse := converse
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext Γ t v
    constructor
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h Γ t s h' := h Γ s t h'

/-!
A sanity check: `⊥ ≠ ⊤` on `TrmRel`, hence `Nontrivial TrmRel`. Without
this the TRA axioms would be vacuously satisfied by the degenerate
one-point carrier, which is not what we want.
-/

theorem bot_ne_top : (⊥ : TrmRel) ≠ ⊤ := by
  intro h
  have hle : (⊤ : TrmRel) ≤ ⊥ := h ▸ le_refl _
  exact hle Unit (Tm.var ()) (Tm.var ()) trivial

instance instNontrivial : Nontrivial TrmRel := ⟨⊥, ⊤, bot_ne_top⟩


end TrmRel

end LeanTra.Instances.PeanoArithmetic
