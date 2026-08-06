/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.InvolutiveQuantale
public import LeanTra.Instances.FirstOrder.Terms

/-!
# Syntax relations on first-order terms

Phase B of the LICS'26 term-model construction: the *carrier* of the
term relation algebra — a family of relations on `Tm S ·`, one per
context, indexed uniformly and closed under renaming — together with the
whole involutive-quantale structure (order, complete lattice, monoid,
`IsQuantale`, `IsInvolutiveQuantale`). The three `SRA`-specific data
(`Δη`, `tilde ·`, `·[·]`) belong to Phase C and are not touched here.

## Contents

* `SynRel S` — the carrier: for every context type `Γ`, a binary relation
  on `Tm S Γ`, uniformly closed under renaming.
* `SynRel.ext` — extensionality via pointwise equivalence of `.rel`.
* Pointwise `⊤`, `⊥`, `⊔`, `⊓`, `sSup`, `sInf` and the `_rel` accessors.
* `PartialOrder`, `CompleteLattice` instances.
* `Mul`, `One`, `Monoid` — composition of relations at the same context,
  with equality as the identity.
* `IsQuantale` — composition distributes over pointwise `sSup`.
* `IsInvolutiveQuantale` — endpoint-swap as the involution.
* `SynRel.bot_ne_top` — the carrier is non-degenerate, as long as some
  type is inhabited (we use `Unit`).

## Design decisions

### (D-B1) Renaming closure, corrected

Example 3(2) of the paper defines a dependent relation `φ : Γ ⇾ Δ` as
"closed under renaming" by requiring, for any renaming `f : i → j`, that
`(t, s) ∈ φ(i)` imply `(t, s) ∈ φ(j)` — *the same pair*. That reading is
only meaningful when `f` is an inclusion and the term sets are literally
nested (as they are in the paper's flat presentation `T(Γ) ⊆ T(V)`).
With renamings declared as arbitrary functions — which the same paper
does, both in §3.1.1 ("maps `ρ : Γ → Δ`") and in Example 3(2) itself
("for any function (renaming) f : i → j") — `f` is never applied and
the condition degenerates: it either holds vacuously (if the two term
sets are disjoint) or reduces to inclusion of one relation into the
other on their intersection. The correct general form, which we take:

  φ Γ t s → φ Δ (t.ren f) (s.ren f)

The paper is internally inconsistent on this point: it declares
renamings to be arbitrary maps but states closure as if they were
inclusions. This file adopts the corrected condition — everything below
is a genuine renaming closure. (Erratum.)

### (D-B2) Per-context composition

Composition quantifies the intermediate term *inside* a single context:

  (φ * ψ) Γ t v  ↔  ∃ u : Tm S Γ, φ Γ t u ∧ ψ Γ u v

not over all terms of all contexts. With contexts-as-types (D1) this
per-context restriction is essentially forced by typing: `φ Γ t u`
requires `u : Tm S Γ`, so an intermediate at a different context does
not type-check without a change-of-context operation on the
composition itself. A "global" flat variant would build that change
of context into the intermediate, and is not the model we take here.

Note. An earlier version of this note cited `□(R * S) ≤ □R * □S` as
an `SRA` theorem justifying per-context composition — that direction
is in fact REFUTED in the term model
(`LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`) and no
longer a valid citation. Only the lax half
`box_mul_box_le : □R * □S ≤ □(R * S)` survives; see the
"Status — open items" section of `Structure/Derived.lean`.

### (D-B3) Pointwise `sSup` / `sInf`

Both `sSup` and `sInf` are computed pointwise, and both preserve
renaming closure (for `sInf`: each member is closed, so the conjunction
is; for `sSup`: apply the closure of the chosen member). Pointwise
`sSup` is precisely what `mul_sSup_distrib` needs, since the
distributivity is then just a swap of two existentials. A
closure-operator-style `sSup` — which `Mathlib.completeLatticeOfInf`
would give us — would break the definitional shape and force us to
prove `sSup` equals the pointwise `∃` before every quantale use. So the
`CompleteLattice` instance is built manually.

## Universes

`SynRel S : Type 1`, because `rel` quantifies over `Γ : Type`. All the
Mathlib typeclasses used here (`Monoid`, `CompleteLattice`, `IsQuantale`,
`IsInvolutiveQuantale`) are `Type u`-polymorphic, so instantiating them
at `Type 1` is unproblematic. No universe issues arose.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, §3.1.1 (syntax and renaming) and Example 3(2)
  (dependent-relation structure; renaming-closure condition —
  cf. (D-B1) for the erratum).
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.FirstOrder

/-- A *syntax relation* on `S`-terms: a family of binary relations on
`Tm S Γ`, one per context type `Γ`, closed under renaming in the sense
of (D-B1) in the module docstring.

Note `SynRel S : Type 1` — see the "Universes" section of the module
docstring. -/
structure SynRel (S : Signature) : Type 1 where
  /-- The underlying context-indexed family of relations. -/
  rel : (Γ : Type) → Tm S Γ → Tm S Γ → Prop
  /-- Uniform renaming closure: transporting both endpoints along any
  `f : Γ → Δ` preserves the relation. This is the corrected form of
  Example 3(2)'s closure clause — see (D-B1). -/
  ren_closed : ∀ {Γ Δ : Type} (f : Γ → Δ) {t s : Tm S Γ},
                 rel Γ t s → rel Δ (t.ren f) (s.ren f)

namespace SynRel

variable {S : Signature}

/-- Extensionality: two `SynRel`s are equal iff their `.rel` fields agree
pointwise. The `ren_closed` field is a `Prop`, so proof irrelevance
absorbs it. -/
@[ext]
theorem ext {φ ψ : SynRel S}
    (h : ∀ Γ (t s : Tm S Γ), φ.rel Γ t s ↔ ψ.rel Γ t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ
  obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by
    funext Γ t s
    exact propext (h Γ t s)
  subst hrel
  rfl

/-! ## Order -/

/-- The order on `SynRel`: pointwise implication of the underlying
relations. -/
instance instLE : LE (SynRel S) :=
  ⟨fun φ ψ => ∀ Γ (t s : Tm S Γ), φ.rel Γ t s → ψ.rel Γ t s⟩

/-- Unfolding of `≤` — pointwise implication. -/
theorem le_iff {φ ψ : SynRel S} :
    φ ≤ ψ ↔ ∀ Γ (t s : Tm S Γ), φ.rel Γ t s → ψ.rel Γ t s :=
  Iff.rfl

/-! ## Pointwise lattice operations

Each of the following instances constructs a `SynRel` via named-field
syntax `{ rel := …, ren_closed := … }` rather than the anonymous
constructor. The anonymous-constructor form triggers Lean's
implicit-lambda insertion at the `ren_closed` field — whose type has
alternating explicit/implicit binders — and mis-binds the proof
argument to an implicit position. Named-field syntax sidesteps the
issue entirely. -/

/-- The universal relation: true on every pair, in every context. -/
instance instTop : Top (SynRel S) := ⟨{
  rel := fun _ _ _ => True
  ren_closed := by intros; trivial
}⟩

/-- The empty relation: false on every pair. -/
instance instBot : Bot (SynRel S) := ⟨{
  rel := fun _ _ _ => False
  ren_closed := by intros _ _ _ _ _ h; exact h.elim
}⟩

/-- Pointwise binary join. -/
instance instMax : Max (SynRel S) := ⟨fun φ ψ => {
  rel := fun Γ t s => φ.rel Γ t s ∨ ψ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    exact h.imp (φ.ren_closed f) (ψ.ren_closed f)
}⟩

/-- Pointwise binary meet. -/
instance instMin : Min (SynRel S) := ⟨fun φ ψ => {
  rel := fun Γ t s => φ.rel Γ t s ∧ ψ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    exact ⟨φ.ren_closed f h.1, ψ.ren_closed f h.2⟩
}⟩

/-- Pointwise arbitrary join — see (D-B3). -/
instance instSupSet : SupSet (SynRel S) := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∃ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩
}⟩

/-- Pointwise arbitrary meet — see (D-B3). -/
instance instInfSet : InfSet (SynRel S) := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∀ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h φ hφ𝒮
    exact φ.ren_closed f (h φ hφ𝒮)
}⟩

/-! ## `.rel` accessors — the pointwise semantics of each operation. -/

/-- `⊤` at the level of `.rel`. -/
@[simp] theorem top_rel {Γ} {t s : Tm S Γ} :
    (⊤ : SynRel S).rel Γ t s ↔ True := Iff.rfl

/-- `⊥` at the level of `.rel`. -/
@[simp] theorem bot_rel {Γ} {t s : Tm S Γ} :
    (⊥ : SynRel S).rel Γ t s ↔ False := Iff.rfl

/-- Pointwise `⊔` at the level of `.rel`. -/
@[simp] theorem sup_rel {φ ψ : SynRel S} {Γ} {t s : Tm S Γ} :
    (φ ⊔ ψ).rel Γ t s ↔ φ.rel Γ t s ∨ ψ.rel Γ t s := Iff.rfl

/-- Pointwise `⊓` at the level of `.rel`. -/
@[simp] theorem inf_rel {φ ψ : SynRel S} {Γ} {t s : Tm S Γ} :
    (φ ⊓ ψ).rel Γ t s ↔ φ.rel Γ t s ∧ ψ.rel Γ t s := Iff.rfl

/-- Pointwise `sSup` at the level of `.rel`. -/
@[simp] theorem sSup_rel {𝒮 : Set (SynRel S)} {Γ} {t s : Tm S Γ} :
    (sSup 𝒮).rel Γ t s ↔ ∃ φ ∈ 𝒮, φ.rel Γ t s := Iff.rfl

/-- Pointwise `sInf` at the level of `.rel`. -/
@[simp] theorem sInf_rel {𝒮 : Set (SynRel S)} {Γ} {t s : Tm S Γ} :
    (sInf 𝒮).rel Γ t s ↔ ∀ φ ∈ 𝒮, φ.rel Γ t s := Iff.rfl

/-- Indexed join at the level of `.rel`. Needed for the quantale
`mul_sSup_distrib` proofs, where the RHS is stated as `⨆ b ∈ s, …`. -/
theorem iSup_rel {ι : Sort*} {f : ι → SynRel S} {Γ} {t s : Tm S Γ} :
    (⨆ i, f i).rel Γ t s ↔ ∃ i, (f i).rel Γ t s := by
  rw [iSup, sSup_rel]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

/-- Bounded indexed join at the level of `.rel`: this is the form the
Mathlib notation `⨆ a ∈ s, f a` expands to. -/
theorem biSup_rel {α : Type*} {s : Set α} {f : α → SynRel S}
    {Γ} {t st : Tm S Γ} :
    (⨆ a ∈ s, f a).rel Γ t st ↔ ∃ a ∈ s, (f a).rel Γ t st := by
  simp only [iSup_rel]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, h⟩

/-! ## Complete lattice -/

/-- The complete lattice structure on `SynRel S`, built manually so that
the pointwise semantics of `sSup`, `sInf`, `⊔`, `⊓`, `⊤`, `⊥` is
preserved definitionally — see (D-B3). -/
instance instCompleteLattice : CompleteLattice (SynRel S) where
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

/-! ## Composition of relations — the monoid structure. -/

/-- Composition of relations, per context (see (D-B2)): the intermediate
term is quantified in the same context as the endpoints. -/
instance instMul : Mul (SynRel S) := ⟨fun φ ψ => {
  rel := fun Γ t v => ∃ u, φ.rel Γ t u ∧ ψ.rel Γ u v
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨u.ren f, φ.ren_closed f htu, ψ.ren_closed f huv⟩
}⟩

/-- Identity of composition: pointwise term equality. -/
instance instOne : One (SynRel S) := ⟨{
  rel := fun _ t s => t = s
  ren_closed := by
    intros _ _ f _ _ h
    exact congrArg (Tm.ren · f) h
}⟩

/-- Composition at the level of `.rel`. -/
@[simp] theorem mul_rel {φ ψ : SynRel S} {Γ} {t v : Tm S Γ} :
    (φ * ψ).rel Γ t v ↔ ∃ u, φ.rel Γ t u ∧ ψ.rel Γ u v := Iff.rfl

/-- Identity at the level of `.rel`. -/
@[simp] theorem one_rel {Γ} {t s : Tm S Γ} :
    (1 : SynRel S).rel Γ t s ↔ t = s := Iff.rfl

/-- The relation monoid: composition is associative with `1` (term
equality) as its two-sided identity. -/
instance instMonoid : Monoid (SynRel S) where
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

/-! ## The quantale structure -/

/-- Composition distributes over arbitrary joins on both sides — the two
`IsQuantale` axioms. Proof is a swap of existentials, made explicit by
first `simp`-normalising both sides through `mul_rel`, `sSup_rel`, and
`biSup_rel`. -/
instance instIsQuantale : IsQuantale (SynRel S) where
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

/-! ## The involutive-quantale structure -/

/-- Endpoint-swap on syntax relations. Preserves renaming closure since
`ren` is applied to both endpoints symmetrically. -/
def converse (φ : SynRel S) : SynRel S := {
  rel := fun Γ t s => φ.rel Γ s t
  ren_closed := by
    intros _ _ f _ _ h
    exact φ.ren_closed f h
}

/-- The involution at the level of `.rel`: endpoint swap. -/
@[simp] theorem converse_rel (φ : SynRel S) {Γ} {t s : Tm S Γ} :
    (converse φ).rel Γ t s ↔ φ.rel Γ s t := Iff.rfl

/-- Composition of relations forms an involutive quantale under the
endpoint-swap involution. -/
instance instIsInvolutiveQuantale : IsInvolutiveQuantale (SynRel S) where
  converse := converse
  converse_converse _ := by ext; rfl
  converse_mul φ ψ := by
    ext Γ t v
    constructor
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_mono _ _ h Γ t s h' := h Γ s t h'

/-! ## Sanity checks -/

/-- The carrier is non-degenerate: `⊥ ≠ ⊤`. Witnessed at
`Γ := Unit`, `t = s = Tm.var ()`, where `⊤` is `True` and `⊥` is
`False`. Contrast with `Instances/Toy.lean`, where `⊤ ≠ ⊥` also holds
but every proper relation is forced to collapse. -/
theorem bot_ne_top : (⊥ : SynRel S) ≠ ⊤ := by
  intro h
  have hle : (⊤ : SynRel S) ≤ ⊥ := h ▸ le_refl _
  exact hle Unit (Tm.var ()) (Tm.var ()) trivial

/-- The carrier is `Nontrivial`. Corollary of `bot_ne_top`. -/
instance instNontrivial : Nontrivial (SynRel S) :=
  ⟨⊥, ⊤, bot_ne_top⟩

end SynRel

end LeanTra.Instances.FirstOrder

#print axioms LeanTra.Instances.FirstOrder.SynRel.instIsInvolutiveQuantale
