/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Syntax.Lambda
public import LeanTra.ToMathlib.Algebra.Order.Quantale.Involutive

/-!
# Relations on λ-terms

Renaming-closed, context-indexed relations on `Lam` form an involutive quantale.

## Main definitions
* `TrmRel`: arity-indexed families of binary relations on `Lam n`, closed under renaming.
* `TrmRel.converse`: the involution swapping the two endpoints of a relation.

## Main statements
* `TrmRel.instCompleteLattice`: pointwise complete lattice on `TrmRel`.
* `TrmRel.instMonoid`, `TrmRel.instIsQuantale`: relational composition as a quantale structure.
* `TrmRel.instIsInvolutiveQuantale`: converse upgrades the quantale to an involutive quantale.

## References

Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
LICS 2026. In particular the bridge theorem for confluence from local
conditions and the Gentzen Inversion and Conservation Principles used
throughout.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

namespace LeanTra.Instances.Lambda

/-! ## Section 2: Renaming-closed context-indexed relations

With the syntax fixed we build the relational layer that will carry
the TRA structure. A TRA does not speak of terms directly but of
*arity-indexed families of relations between terms*, closed under
renaming: this is what `TrmRel` records, a family of binary relations
on `Lam n`, one per arity, uniformly closed along any renaming
`Fin n → Fin m`. On top of `TrmRel` we install the involutive-quantale
operations pointwise per arity: join and meet from set-theoretic union
and intersection, multiplication from relational composition, unit
from the diagonal, and involution from converse. Nothing here is
subtle; the point is simply that the abstract algebra of the TRA
framework has an obvious model on the syntactic side, and everything
reduces to standard facts about binary relations, discharged at
`Type 0` so that no universe bump propagates upward. -/

/-- A *syntax relation*: a family of binary relations on `Lam n`, one
per arity, uniformly closed under renaming. -/
structure TrmRel : Type where
  /-- The underlying arity-indexed family. -/
  rel : (n : Nat) → Lam n → Lam n → Prop
  /-- Renaming closure. -/
  ren_closed : ∀ {n m : Nat} (f : Fin n → Fin m) {t s : Lam n},
                 rel n t s → rel m (t.ren f) (s.ren f)

namespace TrmRel

/-- Extensionality: two `TrmRel`s coincide when their `rel` fields agree
at every arity and every pair of terms. -/
@[ext] theorem ext {φ ψ : TrmRel}
    (h : ∀ n (t s : Lam n), φ.rel n t s ↔ ψ.rel n t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ; obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by funext n t s; exact propext (h n t s)
  subst hrel; rfl

/-! ### The pointwise complete lattice

The first algebraic layer on `TrmRel` is the order structure. The
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
typeclass the abstract framework consumes: the TRA definition demands
a complete lattice on the carrier because that is what makes fixpoint
constructions (Howe-style closures in particular) well-defined. The
proofs of the lattice axioms are elementary, mostly a single `intro`
followed by a projection or an elimination on the pointwise
`∨`/`∧`. -/

/-- Pointwise `≤`. -/
instance instLE : LE TrmRel :=
  ⟨fun φ ψ => ∀ n (t s : Lam n), φ.rel n t s → ψ.rel n t s⟩

/-- Pointwise `⊤`, every pair related at every arity. -/
instance instTop : Top TrmRel := ⟨{
  rel := fun _ _ _ => True
  ren_closed := by intros; trivial }⟩

/-- Pointwise `⊥`, no pair related. -/
instance instBot : Bot TrmRel := ⟨{
  rel := fun _ _ _ => False
  ren_closed := by intros _ _ _ _ _ h; exact h.elim }⟩

/-- Pointwise binary join. -/
instance instMax : Max TrmRel := ⟨fun φ ψ => {
  rel := fun n t s => φ.rel n t s ∨ ψ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h; exact h.imp (φ.ren_closed f) (ψ.ren_closed f) }⟩

/-- Pointwise binary meet. -/
instance instMin : Min TrmRel := ⟨fun φ ψ => {
  rel := fun n t s => φ.rel n t s ∧ ψ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h
    exact ⟨φ.ren_closed f h.1, ψ.ren_closed f h.2⟩ }⟩

/-- Pointwise set-indexed join. -/
instance instSupSet : SupSet TrmRel := ⟨fun 𝒮 => {
  rel := fun n t s => ∃ φ ∈ 𝒮, φ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩ }⟩

/-- Pointwise set-indexed meet. -/
instance instInfSet : InfSet TrmRel := ⟨fun 𝒮 => {
  rel := fun n t s => ∀ φ ∈ 𝒮, φ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h φ hφ𝒮
    exact φ.ren_closed f (h φ hφ𝒮) }⟩

/-- `simp`-normal shape of `⊤`. -/
@[simp] theorem top_rel {n} {t s : Lam n} :
    (⊤ : TrmRel).rel n t s ↔ True := Iff.rfl
/-- `simp`-normal shape of `⊥`. -/
@[simp] theorem bot_rel {n} {t s : Lam n} :
    (⊥ : TrmRel).rel n t s ↔ False := Iff.rfl
/-- `simp`-normal shape of binary join. -/
@[simp] theorem sup_rel {φ ψ : TrmRel} {n} {t s : Lam n} :
    (φ ⊔ ψ).rel n t s ↔ φ.rel n t s ∨ ψ.rel n t s := Iff.rfl
/-- `simp`-normal shape of binary meet. -/
@[simp] theorem inf_rel {φ ψ : TrmRel} {n} {t s : Lam n} :
    (φ ⊓ ψ).rel n t s ↔ φ.rel n t s ∧ ψ.rel n t s := Iff.rfl
/-- `simp`-normal shape of `sSup`. -/
@[simp] theorem sSup_rel {𝒮 : Set TrmRel} {n} {t s : Lam n} :
    (sSup 𝒮).rel n t s ↔ ∃ φ ∈ 𝒮, φ.rel n t s := Iff.rfl
/-- `simp`-normal shape of `sInf`. -/
@[simp] theorem sInf_rel {𝒮 : Set TrmRel} {n} {t s : Lam n} :
    (sInf 𝒮).rel n t s ↔ ∀ φ ∈ 𝒮, φ.rel n t s := Iff.rfl

/-- `simp`-normal shape of indexed supremum. -/
theorem iSup_rel {ι : Sort*} {f : ι → TrmRel} {n} {t s : Lam n} :
    (⨆ i, f i).rel n t s ↔ ∃ i, (f i).rel n t s := by
  rw [iSup, sSup_rel]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

/-- `simp`-normal shape of bounded indexed supremum. -/
theorem biSup_rel {α : Type*} {s : Set α} {f : α → TrmRel}
    {n} {t st : Lam n} :
    (⨆ a ∈ s, f a).rel n t st ↔ ∃ a ∈ s, (f a).rel n t st := by
  simp only [iSup_rel]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩

/-- Pointwise complete lattice structure on `TrmRel`. -/
instance instCompleteLattice : CompleteLattice TrmRel where
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
structure that turns `TrmRel` into an *involutive quantale*, the
carrier the TRA framework actually asks for. Multiplication is
relational composition (`(φ * ψ).rel n t v` iff there is an
intermediate `u` with `φ` on the left and `ψ` on the right), the unit
is the identity relation (equality at every arity), and the
involution is converse (`φᵒ` swaps the two sides). The quantale law
saying that composition distributes over arbitrary joins on both
sides holds essentially by construction: unfolding the definitions
turns it into "an existential over a disjunction is a disjunction of
existentials". The involution laws are equally routine but for the
same reason worth checking explicitly, since the TRA metatheory
manipulates converse freely. Together the four instances close the
involutive-quantale structure and unlock the layer of laws
(`Algebra.InvolutiveQuantale`) on which the TRA operations of Section
3 will be defined. -/

/-- Pointwise relational composition. -/
instance instMul : Mul TrmRel := ⟨fun φ ψ => {
  rel := fun n t v => ∃ u, φ.rel n t u ∧ ψ.rel n u v
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨u.ren f, φ.ren_closed f htu, ψ.ren_closed f huv⟩ }⟩

/-- The identity relation, equality at every arity. -/
instance instOne : One TrmRel := ⟨{
  rel := fun _ t s => t = s
  ren_closed := by intros _ _ f _ _ h; exact congrArg (Lam.ren · f) h }⟩

/-- `simp`-normal shape of composition. -/
@[simp] theorem mul_rel {φ ψ : TrmRel} {n} {t v : Lam n} :
    (φ * ψ).rel n t v ↔ ∃ u, φ.rel n t u ∧ ψ.rel n u v := Iff.rfl
/-- `simp`-normal shape of the identity relation. -/
@[simp] theorem one_rel {n} {t s : Lam n} :
    (1 : TrmRel).rel n t s ↔ t = s := Iff.rfl

/-- Monoid structure on `TrmRel` under composition and equality. -/
instance instMonoid : Monoid TrmRel where
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
instance instIsQuantale : IsQuantale TrmRel where
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
def converse (φ : TrmRel) : TrmRel := {
  rel := fun n t s => φ.rel n s t
  ren_closed := by intros _ _ f _ _ h; exact φ.ren_closed f h }

/-- `simp`-normal shape of converse. -/
@[simp] theorem converse_rel (φ : TrmRel) {n} {t s : Lam n} :
    (converse φ).rel n t s ↔ φ.rel n s t := Iff.rfl

/-- The involutive-quantale layer: `converse` is an involutive
anti-endomorphism of the quantale. -/
instance instIsInvolutiveQuantale : IsInvolutiveQuantale TrmRel where
  converse := converse
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext n t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h n t s h' := h n s t h'

end TrmRel
end LeanTra.Instances.Lambda
