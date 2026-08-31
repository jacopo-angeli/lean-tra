/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
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
public import LeanTra.Nominal.Basic
public import LeanTra.Instances.SecondOrder.Lambda.Syntax
public import LeanTra.Instances.SecondOrder.Lambda.Substitution

/-!
# The (untyped) λ-calculus as a second-order SRA instance

Second-order counterpart of `Instances/FirstOrder/*`, specialised to
the binding signature of the λ-calculus (`lam : (1)`, `app : (0,0)`),
following LICS'26 §3.1.2 and Example 22 (β as an orthogonal rule).

## Structure

The syntax and substitution layers live in dedicated modules:

* `LeanTra.Nominal.Basic` — the nominal foundation (`Atom`, `Perm`,
  `IsNominal`, support, freshness). Signature-agnostic.
* `LeanTra.Instances.SecondOrder.Lambda.Syntax` — named raw terms
  `RawLam`, α-equivalence, α-quotient `Lam = 𝒯Σᵅ(V)`, `Lam` as a
  nominal set, `Lam.fv` and its equivariance.
* `LeanTra.Instances.SecondOrder.Lambda.Substitution` — the `Subst`
  structure (finite-support `Atom → Lam`), `RawLam.subst`,
  `Lam.subst`, `Perm`-action on substitutions.

This file (the "top" of the tower) provides:

1. `SynRel'` — equivariant relations on `Lam`; the involutive quantale.
2. `SRA' SynRel'` — the four SRA operations `varDiag`, `scr`, `subst`,
   `j` and the sixteen SRA axioms.
3. `OperationalDecomposition' SynRel'` — `introduction` and
   `elimination` with the thirteen OpDecomp axioms.
4. `betaRule' : SynRel'` — β-reduction, with the five rule-side
   conditions of `local_confluence`.
5. `betaRule'_local_confluent` — confluence of parallel β, via the
   bridge theorem.

## Representation choices

The paper uses named second-order syntax with α-equivalence quotient.
Concretely: `Atom := Nat` (opaque wrapper via `abbrev`), `Perm :=
Equiv.Perm Atom`, `Lam := Quotient RawLam.instSetoid` where the
setoid is the α-equivalence relation. Substitutions are bundled in
`Subst` with an explicit finite support (Def. 12 of the paper).

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System
  Metatheory.* LICS 2026. §3.1.2 (second-order syntax), Example 22
  (β-reduction as orthogonal).
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA
open LeanTra.Algebra

namespace LeanTra.Instances.Lambda

namespace Named

open LeanTra.Nominal

/-! ## Section 2' — Equivariant relations on `Lam`

The relation algebra for the paper's second-order syntax. Per §3.1.2.1
of the paper, term relations should be "equivariant finitely
supported"; but equivariant relations have support `∅` automatically,
and all the constructions we build (`varDiag`, `scr`, `subst`, `j`)
are equivariant. So we work with equivariant relations directly and
the FS layer is dispensable at the SynRel level. -/

/-- An **equivariant relation** on `Lam` — a binary relation on the
α-quotient that commutes with the `Perm` action. This is the paper's
`(𝒯Σᵅ(V))²` restricted to the equivariant slice, and it forms an
involutive quantale (and eventually an SRA). -/
structure SynRel' where
  /-- The underlying relation. -/
  rel : Lam → Lam → Prop
  /-- Preserved by the permutation action on both sides. -/
  equivariant : ∀ (π : Perm) (t s : Lam), rel t s → rel (π • t) (π • s)

namespace SynRel'

@[ext] theorem ext {φ ψ : SynRel'}
    (h : ∀ t s, φ.rel t s ↔ ψ.rel t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ; obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by funext t s; exact propext (h t s)
  subst hrel; rfl

/-! ### Order and lattice operations -/

instance instLE : LE SynRel' :=
  ⟨fun φ ψ => ∀ t s, φ.rel t s → ψ.rel t s⟩

instance instTop : Top SynRel' := ⟨{
  rel := fun _ _ => True
  equivariant := by intros; trivial }⟩

instance instBot : Bot SynRel' := ⟨{
  rel := fun _ _ => False
  equivariant := by intros _ _ _ h; exact h.elim }⟩

instance instMax : Max SynRel' := ⟨fun φ ψ => {
  rel := fun t s => φ.rel t s ∨ ψ.rel t s
  equivariant := by
    intros π t s h; exact h.imp (φ.equivariant π t s) (ψ.equivariant π t s) }⟩

instance instMin : Min SynRel' := ⟨fun φ ψ => {
  rel := fun t s => φ.rel t s ∧ ψ.rel t s
  equivariant := by
    intros π t s h
    exact ⟨φ.equivariant π t s h.1, ψ.equivariant π t s h.2⟩ }⟩

instance instSupSet : SupSet SynRel' := ⟨fun 𝒮 => {
  rel := fun t s => ∃ φ ∈ 𝒮, φ.rel t s
  equivariant := by
    intros π t s h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.equivariant π t s h⟩ }⟩

instance instInfSet : InfSet SynRel' := ⟨fun 𝒮 => {
  rel := fun t s => ∀ φ ∈ 𝒮, φ.rel t s
  equivariant := by
    intros π t s h φ hφ𝒮
    exact φ.equivariant π t s (h φ hφ𝒮) }⟩

@[simp] theorem top_rel {t s : Lam} :
    (⊤ : SynRel').rel t s ↔ True := Iff.rfl
@[simp] theorem bot_rel {t s : Lam} :
    (⊥ : SynRel').rel t s ↔ False := Iff.rfl
@[simp] theorem sup_rel {φ ψ : SynRel'} {t s : Lam} :
    (φ ⊔ ψ).rel t s ↔ φ.rel t s ∨ ψ.rel t s := Iff.rfl
@[simp] theorem inf_rel {φ ψ : SynRel'} {t s : Lam} :
    (φ ⊓ ψ).rel t s ↔ φ.rel t s ∧ ψ.rel t s := Iff.rfl
@[simp] theorem sSup_rel {𝒮 : Set SynRel'} {t s : Lam} :
    (sSup 𝒮).rel t s ↔ ∃ φ ∈ 𝒮, φ.rel t s := Iff.rfl
@[simp] theorem sInf_rel {𝒮 : Set SynRel'} {t s : Lam} :
    (sInf 𝒮).rel t s ↔ ∀ φ ∈ 𝒮, φ.rel t s := Iff.rfl

theorem iSup_rel {ι : Sort*} {f : ι → SynRel'} {t s : Lam} :
    (⨆ i, f i).rel t s ↔ ∃ i, (f i).rel t s := by
  rw [iSup, sSup_rel]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

theorem biSup_rel {α : Type*} {s : Set α} {f : α → SynRel'}
    {t st : Lam} :
    (⨆ a ∈ s, f a).rel t st ↔ ∃ a ∈ s, (f a).rel t st := by
  simp only [iSup_rel]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩

instance instCompleteLattice : CompleteLattice SynRel' where
  le := (· ≤ ·)
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ t s h := h₂ t s (h₁ t s h)
  le_antisymm φ ψ h₁ h₂ := by ext t s; exact ⟨h₁ t s, h₂ t s⟩
  sup := (· ⊔ ·)
  le_sup_left _ _ _ _ h := Or.inl h
  le_sup_right _ _ _ _ h := Or.inr h
  sup_le _ _ _ h₁ h₂ t s h := h.elim (h₁ t s) (h₂ t s)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ t s h := ⟨h₁ t s h, h₂ t s h⟩
  sSup := sSup
  isLUB_sSup 𝒮 :=
    ⟨fun φ hφ𝒮 t s h => ⟨φ, hφ𝒮, h⟩,
     fun _ hb t s => by
       rintro ⟨φ, hφ𝒮, h⟩; exact hb hφ𝒮 t s h⟩
  sInf := sInf
  isGLB_sInf 𝒮 :=
    ⟨fun φ hφ𝒮 t s h => h φ hφ𝒮,
     fun _ hb t s h φ hφ𝒮 => hb hφ𝒮 t s h⟩
  top := ⊤
  le_top _ _ _ _ := trivial
  bot := ⊥
  bot_le _ _ _ h := h.elim

/-! ### Composition, identity, quantale, involution -/

instance instMul : Mul SynRel' := ⟨fun φ ψ => {
  rel := fun t v => ∃ u, φ.rel t u ∧ ψ.rel u v
  equivariant := by
    intros π t v h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨π • u, φ.equivariant π t u htu, ψ.equivariant π u v huv⟩ }⟩

instance instOne : One SynRel' := ⟨{
  rel := fun t s => t = s
  equivariant := by intros _ _ _ h; exact congrArg _ h }⟩

@[simp] theorem mul_rel {φ ψ : SynRel'} {t v : Lam} :
    (φ * ψ).rel t v ↔ ∃ u, φ.rel t u ∧ ψ.rel u v := Iff.rfl
@[simp] theorem one_rel {t s : Lam} :
    (1 : SynRel').rel t s ↔ t = s := Iff.rfl

instance instMonoid : Monoid SynRel' where
  mul := (· * ·)
  one := 1
  one_mul φ := by
    ext t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, rfl, h⟩; exact h
    · intro h; exact ⟨t, rfl, h⟩
  mul_one φ := by
    ext t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, h, rfl⟩; exact h
    · intro h; exact ⟨v, h, rfl⟩
  mul_assoc φ ψ χ := by
    ext t w
    refine ⟨?_, ?_⟩
    · rintro ⟨v, ⟨u, htu, huv⟩, hvw⟩; exact ⟨u, htu, v, huv, hvw⟩
    · rintro ⟨u, htu, v, huv, hvw⟩; exact ⟨v, ⟨u, htu, huv⟩, hvw⟩

instance instIsQuantale : IsQuantale SynRel' where
  mul_sSup_distrib a 𝒮 := by
    ext t v
    rw [mul_rel, biSup_rel]
    simp only [mul_rel, sSup_rel]
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hau, φ, hφ, hφuv⟩; exact ⟨φ, hφ, u, hau, hφuv⟩
    · rintro ⟨φ, hφ, u, hau, hφuv⟩; exact ⟨u, hau, φ, hφ, hφuv⟩
  sSup_mul_distrib 𝒮 a := by
    ext t v
    rw [mul_rel, biSup_rel]
    simp only [mul_rel, sSup_rel]
    refine ⟨?_, ?_⟩
    · rintro ⟨u, ⟨φ, hφ, hφtu⟩, hau⟩; exact ⟨φ, hφ, u, hφtu, hau⟩
    · rintro ⟨φ, hφ, u, hφtu, hau⟩; exact ⟨u, ⟨φ, hφ, hφtu⟩, hau⟩

def converse (φ : SynRel') : SynRel' := {
  rel := fun t s => φ.rel s t
  equivariant := by intros π t s h; exact φ.equivariant π s t h }

@[simp] theorem converse_rel (φ : SynRel') {t s : Lam} :
    (converse φ).rel t s ↔ φ.rel s t := Iff.rfl

instance instIsInvolutiveQuantale : IsInvolutiveQuantale SynRel' where
  converse := converse
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h t s h' := h s t h'

end SynRel'

/-! ### SRA operations on `SynRel'`

The four operations of an SRA — `varDiag`, `scr`, `subst`, `j` — as
equivariant relations on `Lam`. `subst` uses `Subst` (Task 3). All
four are equivariant by construction. -/

namespace SynRel'

/-- `Δη`: pairs of the same variable. -/
def varDiag : SynRel' where
  rel := fun t s => ∃ x : Atom, t = Lam.var x ∧ s = Lam.var x
  equivariant := by
    rintro π t s ⟨x, rfl, rfl⟩
    refine ⟨π • x, ?_, ?_⟩ <;> simp

@[simp] theorem varDiag_rel {t s : Lam} :
    varDiag.rel t s ↔ ∃ x : Atom, t = Lam.var x ∧ s = Lam.var x := Iff.rfl

/-- Strict compatible refinement: same outermost constructor with
sub-terms pairwise `φ`-related. The `lam` clause exists at the bound
name (which can be α-renamed freely since `φ` is equivariant). -/
def scr (φ : SynRel') : SynRel' where
  rel := fun t s =>
    (∃ a t' s', t = Lam.lam a t' ∧ s = Lam.lam a s' ∧ φ.rel t' s')
    ∨ (∃ t₁ t₂ s₁ s₂, t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
        ∧ φ.rel t₁ s₁ ∧ φ.rel t₂ s₂)
  equivariant := by
    intro π t s h
    rcases h with ⟨a, t', s', rfl, rfl, hφ⟩
                | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩
    · refine Or.inl ⟨π • a, π • t', π • s', ?_, ?_, ?_⟩
      · simp
      · simp
      · exact φ.equivariant π t' s' hφ
    · refine Or.inr ⟨π • t₁, π • t₂, π • s₁, π • s₂, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · exact φ.equivariant π t₁ s₁ hφ₁
      · exact φ.equivariant π t₂ s₂ hφ₂

@[simp] theorem scr_rel {φ : SynRel'} {t s : Lam} :
    (scr φ).rel t s ↔
      (∃ a t' s', t = Lam.lam a t' ∧ s = Lam.lam a s' ∧ φ.rel t' s')
      ∨ (∃ t₁ t₂ s₁ s₂, t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
          ∧ φ.rel t₁ s₁ ∧ φ.rel t₂ s₂) := Iff.rfl

/-- `subst φ ψ`: pairs obtained by substitution witnesses. The pointwise
`ψ`-obligation is restricted to `fv t ∪ fv s`, matching the paper's
`Γ`-context semantics (Def. 12) — outside of `Γ`, the substitution
acts as identity and the obligation would be trivial (or impossible
for non-reflexive `ψ`). -/
def subst (φ ψ : SynRel') : SynRel' where
  rel := fun u v =>
    ∃ (τ σ : Subst) (t s : Lam),
      φ.rel t s ∧ (∀ x ∈ Lam.fv t ∪ Lam.fv s, ψ.rel (τ x) (σ x))
      ∧ u = Lam.subst τ t ∧ v = Lam.subst σ s
  equivariant := by
    rintro π u v ⟨τ, σ, t, s, hφ, hψ, rfl, rfl⟩
    refine ⟨π • τ, π • σ, π • t, π • s, φ.equivariant π t s hφ,
      ?_, ?_, ?_⟩
    · intro x hx
      -- x ∈ fv (π • t) ∪ fv (π • s) = (fv t ∪ fv s).image (π • ·)
      rw [Lam.fv_smul, Lam.fv_smul, ← Finset.image_union] at hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      subst hxy
      show ψ.rel ((π • τ).toFun (π • y)) ((π • σ).toFun (π • y))
      rw [Subst.smul_apply, Subst.smul_apply]
      have : π⁻¹ • π • y = y := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [this]
      exact ψ.equivariant π _ _ (hψ y hy)
    · exact Lam.subst_smul π τ t
    · exact Lam.subst_smul π σ s

@[simp] theorem subst_rel {φ ψ : SynRel'} {u v : Lam} :
    (subst φ ψ).rel u v ↔
      ∃ (τ σ : Subst) (t s : Lam),
        φ.rel t s ∧ (∀ x ∈ Lam.fv t ∪ Lam.fv s, ψ.rel (τ x) (σ x))
        ∧ u = Lam.subst τ t ∧ v = Lam.subst σ s := Iff.rfl

/-- Closure constant `j`: pairs where both are closed terms. -/
def j : SynRel' where
  rel := fun t s => t = s ∧ Lam.fv t = ∅
  equivariant := by
    rintro π t s ⟨rfl, hcl⟩
    refine ⟨rfl, ?_⟩
    rw [Lam.fv_smul, hcl, Finset.image_empty]

@[simp] theorem j_rel {t s : Lam} :
    j.rel t s ↔ t = s ∧ Lam.fv t = ∅ := Iff.rfl

/-! ### Easy SRA axioms (non-FSP-dependent)

These 11 axioms don't require the FSP argument in the `lam` case.
They follow directly from the definitions. The 5 FSP-based axioms
(`subst_scr_oplaxity`, `subst_associativity_ge`,
`subst_introduction_oplaxity`, `elimination_join_preservation_le`,
`box_elimination_oplaxity`) require choosing a fresh binder atom
outside the substitution's support — those are deferred as `sorry`s
inside the SRA instance below. -/

theorem varDiag_symmetry : (varDiag)ᵒ ≤ varDiag := by
  intro t s ⟨x, hs, ht⟩; exact ⟨x, ht, hs⟩

theorem varDiag_cotransitivity : varDiag ≤ varDiag * varDiag := by
  intro t s ⟨x, ht, hs⟩
  exact ⟨Lam.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

theorem scr_monotonicity {φ ψ : SynRel'} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro t s hs
  rcases hs with ⟨a, t', s', ht, hs', hφ⟩ | ⟨t₁, t₂, s₁, s₂, ht, hs', hφ₁, hφ₂⟩
  · exact Or.inl ⟨a, t', s', ht, hs', h _ _ hφ⟩
  · exact Or.inr ⟨t₁, t₂, s₁, s₂, ht, hs', h _ _ hφ₁, h _ _ hφ₂⟩

theorem scr_converse_commutation (φ : SynRel') : scr (φᵒ) = (scr φ)ᵒ := by
  ext t s
  refine ⟨?_, ?_⟩
  · rintro (⟨a, t', s', rfl, rfl, hφ⟩
            | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨a, s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩
  · rintro (⟨a, t', s', rfl, rfl, hφ⟩
            | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨a, s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩

theorem subst_monotonicity_right {φ ψ ψ' : SynRel'} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  rintro u v ⟨τ, σ, t, s, hφ, hψ, ht, hs⟩
  exact ⟨τ, σ, t, s, hφ, fun x hx => h _ _ (hψ x hx), ht, hs⟩

/-- Constructors of `Lam` are distinct: `var x ≠ lam a u`. -/
theorem Lam_var_ne_lam (x : Atom) (a : Atom) (u : Lam) :
    Lam.var x ≠ Lam.lam a u := by
  refine Quotient.inductionOn u ?_
  intro raw h
  have := Quotient.exact h
  cases this

/-- Constructors of `Lam` are distinct: `var x ≠ app u v`. -/
theorem Lam_var_ne_app (x : Atom) (u v : Lam) :
    Lam.var x ≠ Lam.app u v := by
  refine Quotient.inductionOn₂ u v ?_
  intro rawu rawv h
  have := Quotient.exact h
  cases this

/-- Constructors of `Lam` are distinct: `lam a u ≠ app v w`. -/
theorem Lam_lam_ne_app (a : Atom) (u v w : Lam) :
    Lam.lam a u ≠ Lam.app v w := by
  refine Quotient.inductionOn u ?_
  intro rawu
  refine Quotient.inductionOn₂ v w ?_
  intro rawv raww h
  have := Quotient.exact h
  cases this

/-- Injectivity of `Lam.app`: reduces to `RawLam.app` injectivity via α. -/
theorem Lam_app_inj {u₁ u₂ v₁ v₂ : Lam}
    (h : Lam.app u₁ u₂ = Lam.app v₁ v₂) : u₁ = v₁ ∧ u₂ = v₂ := by
  refine Quotient.inductionOn₂ u₁ u₂ (fun ru₁ ru₂ =>
    Quotient.inductionOn₂ v₁ v₂ (fun rv₁ rv₂ (h : _) => ?_)) h
  have hae := Quotient.exact h
  cases hae with
  | app h₁ h₂ => exact ⟨Quotient.sound h₁, Quotient.sound h₂⟩

/-- Injectivity of `Lam.lam` at the same binder atom: reduces to
`AlphaEq` on the bodies via the cofinite-`swap` argument, using
`AlphaEq.smul` and `swap_swap` to strip the swap. -/
theorem Lam_lam_inj_same {a : Atom} {u v : Lam}
    (h : Lam.lam a u = Lam.lam a v) : u = v := by
  refine Quotient.inductionOn₂ u v (fun ru rv (h : _) => ?_) h
  have hae : AlphaEq (RawLam.lam a ru) (RawLam.lam a rv) := Quotient.exact h
  cases hae with
  | @lam _ _ _ _ L hL =>
    apply Quotient.sound
    obtain ⟨c, hc⟩ := LeanTra.Nominal.exists_notMem L
    have hLc := hL c hc
    have hSmul := AlphaEq.smul (swap a c) hLc
    simp only [← mul_smul, Equiv.swap_mul_self, one_smul] at hSmul
    exact hSmul

theorem varDiag_scr_orthogonality (φ : SynRel') :
    varDiag * scr φ ≤ ⊥ := by
  rintro t v ⟨u, ⟨x, _, rfl⟩, h⟩
  rcases h with ⟨a, _, _, hu, _⟩ | ⟨_, _, _, _, hu, _, _, _⟩
  · exact Lam_var_ne_lam x a _ hu
  · exact Lam_var_ne_app x _ _ hu

/-! ### The SRA instance

Full instance with 11 axioms proved and 5 marked `sorry` for the
FSP-based ones (per docstring above). Each `sorry` corresponds to a
specific paper claim that requires nominal freshness reasoning; see
also the `sorry`s in `subst` and `j` above (for equivariance of
`Lam.subst` and `Lam.fv`, which propagate). -/

instance instSRA : SRA SynRel' where
  varDiag := varDiag
  scr := scr
  subst := subst
  varDiag_symmetry := varDiag_symmetry
  varDiag_cotransitivity := varDiag_cotransitivity
  scr_monotonicity := fun _ _ h => scr_monotonicity h
  scr_compositionality := by
    intro φ ψ
    ext t v
    refine ⟨?_, ?_⟩
    · -- (≤): scr (φ * ψ) ≤ scr φ * scr ψ
      rintro (⟨a, t', v', rfl, rfl, u', hφ, hψ⟩
              | ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨u₁, hφ₁, hψ₁⟩,
                 ⟨u₂, hφ₂, hψ₂⟩⟩)
      · exact ⟨Lam.lam a u', Or.inl ⟨a, t', u', rfl, rfl, hφ⟩,
                              Or.inl ⟨a, u', v', rfl, rfl, hψ⟩⟩
      · exact ⟨Lam.app u₁ u₂,
               Or.inr ⟨t₁, t₂, u₁, u₂, rfl, rfl, hφ₁, hφ₂⟩,
               Or.inr ⟨u₁, u₂, v₁, v₂, rfl, rfl, hψ₁, hψ₂⟩⟩
    · -- (≥): scr φ * scr ψ ≤ scr (φ * ψ)
      rintro ⟨u, hφ, hψ⟩
      rcases hφ with ⟨a, t', u', rfl, hu, hφ⟩
                    | ⟨t₁, t₂, u₁, u₂, rfl, hu, hφ₁, hφ₂⟩
      · rcases hψ with ⟨b, u'', v', hu', rfl, hψ⟩
                      | ⟨_, _, _, _, hu', _, _, _⟩
        · -- Both lam-shapes: u = lam a u' = lam b u''
          by_cases hab : a = b
          · subst hab
            have hueq : u' = u'' := Lam_lam_inj_same (hu.symm.trans hu')
            subst hueq
            exact Or.inl ⟨a, t', v', rfl, rfl, u', hφ, hψ⟩
          · -- a ≠ b. Pick c fresh for u', u'', t', v', {a, b}.
            obtain ⟨c, hc⟩ := LeanTra.Nominal.exists_notMem
              (Lam.fv u' ∪ Lam.fv u'' ∪ Lam.fv t' ∪ Lam.fv v' ∪ {a, b})
            simp only [Finset.mem_union, not_or] at hc
            obtain ⟨⟨⟨⟨hcu', hcu''⟩, hct'⟩, hcv'⟩, _⟩ := hc
            -- Rename all binders to c
            have het : Lam.lam a t' = Lam.lam c (swap a c • t') :=
              Lam.lam_alpha a c t' (Or.inl hct')
            have hev : Lam.lam b v' = Lam.lam c (swap b c • v') :=
              Lam.lam_alpha b c v' (Or.inl hcv')
            have heu1 : Lam.lam a u' = Lam.lam c (swap a c • u') :=
              Lam.lam_alpha a c u' (Or.inl hcu')
            have heu2 : Lam.lam b u'' = Lam.lam c (swap b c • u'') :=
              Lam.lam_alpha b c u'' (Or.inl hcu'')
            -- From u = lam a u' = lam b u'', get swap a c • u' = swap b c • u''
            have hueq : swap a c • u' = swap b c • u'' := by
              apply Lam_lam_inj_same (a := c)
              rw [← heu1, ← heu2, hu.symm.trans hu']
            refine Or.inl ⟨c, swap a c • t', swap b c • v', het, hev, ?_⟩
            refine ⟨swap a c • u', ?_, ?_⟩
            · exact φ.equivariant (swap a c) t' u' hφ
            · rw [hueq]
              exact ψ.equivariant (swap b c) u'' v' hψ
        · exact absurd (hu.symm.trans hu') (Lam_lam_ne_app _ _ _ _)
      · rcases hψ with ⟨_, _, _, hu', _⟩
                      | ⟨u₁', u₂', v₁, v₂, hu', rfl, hψ₁, hψ₂⟩
        · exact absurd (hu'.symm.trans hu) (Lam_lam_ne_app _ _ _ _)
        · have hinj : Lam.app u₁ u₂ = Lam.app u₁' u₂' := hu.symm.trans hu'
          obtain ⟨heq₁, heq₂⟩ := Lam_app_inj hinj
          subst heq₁
          subst heq₂
          exact Or.inr ⟨t₁, t₂, v₁, v₂, rfl, rfl,
                        ⟨u₁, hφ₁, hψ₁⟩, ⟨u₂, hφ₂, hψ₂⟩⟩
  scr_converse_commutation := scr_converse_commutation
  varDiag_scr_orthogonality := varDiag_scr_orthogonality
  subst_monotonicity_right := fun _ _ _ h => subst_monotonicity_right h
  subst_compositionality_oplax := by
    -- Given u = Lam.subst τ t, v = Lam.subst σ s with (t, s) ∈ φ * φ' via w,
    -- pointwise (ψ * ψ')-related τ, σ. Choose μ pointwise to split; the
    -- intermediate substitution needs a finite-support witness which requires
    -- axiom of choice on a possibly-infinite family. Deferred.
    sorry
  subst_converse_commutation := by
    intro φ ψ
    ext u v
    refine ⟨?_, ?_⟩
    · rintro ⟨τ, σ, t, s, hφ, hψ, hv, hu⟩
      refine ⟨σ, τ, s, t, hφ, ?_, hu, hv⟩
      intro x hx
      rw [Finset.union_comm] at hx
      exact hψ x hx
    · rintro ⟨τ, σ, t, s, hφ, hψ, hu, hv⟩
      refine ⟨σ, τ, s, t, hφ, ?_, hv, hu⟩
      intro x hx
      rw [Finset.union_comm] at hx
      exact hψ x hx
  subst_join_preservation_left := by
    intro 𝒮 ψ
    ext u v
    refine ⟨?_, ?_⟩
    · rintro ⟨τ, σ, t, s, ⟨φ, hφ𝒮, hφ⟩, hψ, hu, hv⟩
      exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, τ, σ, t, s, hφ, hψ, hu, hv⟩
    · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, τ, σ, t, s, hφ, hψ, hu, hv⟩
      exact ⟨τ, σ, t, s, ⟨φ, hφ𝒮, hφ⟩, hψ, hu, hv⟩
  subst_varDiag_unit_left := by
    intro ψ
    ext u v
    refine ⟨?_, ?_⟩
    · rintro ⟨τ, σ, _, _, ⟨x, rfl, rfl⟩, hψ, rfl, rfl⟩
      -- u = subst τ (var x) = τ x, v = σ x
      simp only [Lam.subst_var]
      have hx : x ∈ Lam.fv (Lam.var x) ∪ Lam.fv (Lam.var x) := by
        simp [Lam.fv_var]
      exact hψ x hx
    · intro hψ
      -- ψ.rel u v. Build witnesses using x = 0.
      refine ⟨Subst.id.update 0 u, Subst.id.update 0 v,
              Lam.var 0, Lam.var 0, ⟨0, rfl, rfl⟩, ?_, ?_, ?_⟩
      · intro y hy
        -- hy : y ∈ fv (var 0) ∪ fv (var 0) = {0}, so y = 0
        have hy0 : y = 0 := by simp [Lam.fv_var] at hy; exact hy
        subst hy0
        show ψ.rel ((Subst.id.update 0 u).toFun 0)
                   ((Subst.id.update 0 v).toFun 0)
        rw [Subst.update_apply_same, Subst.update_apply_same]
        exact hψ
      · show u = Lam.subst _ (Lam.var 0)
        rw [Lam.subst_var]
        exact (Subst.update_apply_same _ _ _).symm
      · show v = Lam.subst _ (Lam.var 0)
        rw [Lam.subst_var]
        exact (Subst.update_apply_same _ _ _).symm
  subst_varDiag_unit_right := by
    intro φ
    apply le_antisymm
    · -- (≤): subst φ varDiag ≤ φ. Deferred — requires extending a partial
      -- renaming (from pointwise varDiag witnesses) to a Perm and closing
      -- via φ's equivariance.
      sorry
    · -- (≥): φ ≤ subst φ varDiag. Take τ = σ = Subst.id, t = u, s = v.
      intro u v hφ
      refine ⟨Subst.id, Subst.id, u, v, hφ, ?_, ?_, ?_⟩
      · intro x _
        exact ⟨x, rfl, rfl⟩
      · exact (Lam.subst_id u).symm
      · exact (Lam.subst_id v).symm
  subst_associativity := by
    -- Kleisli associativity. The (≥) direction is FSP-based.
    sorry
  subst_scr_oplaxity := by
    -- Unpack a `subst (scr φ) ψ` witness. The `app` case is purely
    -- structural — the outer `scr` clause survives substitution term
    -- by term. The `lam` case requires reasoning about how `Lam.subst`
    -- computes on a `Lam.lam`, i.e. a clean `Lam.subst_lam` lemma
    -- (fresh-atom + inner-body substitution), which in turn rests on
    -- the sorry'd `RawLam.subst_alpha`. Deferred.
    intro φ ψ u v h
    obtain ⟨τ, σ, t, s, hscr, hψ, rfl, rfl⟩ := h
    rcases hscr with ⟨a, t', s', rfl, rfl, hφ⟩
                   | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩
    · -- lam case: needs `Lam.subst_lam` (fresh-atom computation).
      sorry
    · -- app case: `Lam.subst_app` computes; the outer `scr` (app clause)
      -- lifts through with `subst φ ψ` witnesses on each argument.
      simp only [Lam.subst_app]
      refine Or.inr ⟨Lam.subst τ t₁, Lam.subst τ t₂,
              Lam.subst σ s₁, Lam.subst σ s₂, rfl, rfl, ?_, ?_⟩
      · refine ⟨τ, σ, t₁, s₁, hφ₁, ?_, rfl, rfl⟩
        intro x hx
        apply hψ x
        simp only [Lam.fv_app, Finset.mem_union] at hx ⊢
        rcases hx with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · refine ⟨τ, σ, t₂, s₂, hφ₂, ?_, rfl, rfl⟩
        intro x hx
        apply hψ x
        simp only [Lam.fv_app, Finset.mem_union] at hx ⊢
        rcases hx with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
  cr_fixpoint := by
    ext t s
    refine ⟨?_, ?_⟩
    · rintro (⟨x, rfl, rfl⟩
              | (⟨a, t', s', rfl, rfl, (h : t' = s')⟩
                 | ⟨t₁, t₂, s₁, s₂, rfl, rfl, (h₁ : t₁ = s₁), (h₂ : t₂ = s₂)⟩))
      · rfl
      · exact congrArg _ h
      · exact congrArg₂ _ h₁ h₂
    · intro (h : t = s)
      subst h
      refine Quotient.inductionOn t ?_
      intro raw
      induction raw with
      | var x => exact Or.inl ⟨x, rfl, rfl⟩
      | app t₁ t₂ _ _ =>
          exact Or.inr (Or.inr ⟨Lam.mk t₁, Lam.mk t₂, Lam.mk t₁,
                                Lam.mk t₂, rfl, rfl, rfl, rfl⟩)
      | lam a t' _ =>
          exact Or.inr (Or.inl ⟨a, Lam.mk t', Lam.mk t', rfl, rfl, rfl⟩)
  cr_induction := by
    intro φ h t s (heq : t = s)
    subst heq
    refine Quotient.inductionOn t ?_
    intro raw
    induction raw with
    | var x =>
        apply h
        exact Or.inl ⟨x, rfl, rfl⟩
    | app t₁ t₂ iht₁ iht₂ =>
        apply h
        exact Or.inr (Or.inr ⟨Lam.mk t₁, Lam.mk t₂, Lam.mk t₁,
                              Lam.mk t₂, rfl, rfl, iht₁, iht₂⟩)
    | lam a t' iht' =>
        apply h
        exact Or.inr (Or.inl ⟨a, Lam.mk t', Lam.mk t', rfl, rfl, iht'⟩)
  j := j
  j_coreflexivity := fun _ _ h => h.1
  j_symmetry := by
    rintro t s ⟨hst, hcl⟩
    -- Symmetric closure at closed terms.
    refine ⟨hst.symm, ?_⟩
    -- hcl : Lam.fv s = ∅ (was renamed via hst)
    rw [← hst]; exact hcl
  j_cotransitivity := by
    rintro t s ⟨rfl, hcl⟩
    exact ⟨t, ⟨rfl, hcl⟩, ⟨rfl, hcl⟩⟩
  j_varDiag_orthogonality := by
    rintro t v ⟨u, ⟨htu, hclu⟩, ⟨x, huvar, _⟩⟩
    subst htu
    subst huvar
    simp at hclu

/-! ### OperationalDecomposition operations

`introduction a` isolates the `lam` clause of `scr a`; `elimination a b`
isolates the `app` clause, split into major (`a`-related) and minor
(`b`-related) arguments. Together they refine `scr`. -/

/-- Introduction forms: `(lam a t, lam a s)` with `a`-related bodies. -/
def introduction (a : SynRel') : SynRel' where
  rel := fun t s => ∃ x t' s', t = Lam.lam x t' ∧ s = Lam.lam x s' ∧ a.rel t' s'
  equivariant := by
    rintro π t s ⟨x, t', s', rfl, rfl, ha⟩
    refine ⟨π • x, π • t', π • s', ?_, ?_, a.equivariant π t' s' ha⟩ <;> simp

@[simp] theorem introduction_rel {a : SynRel'} {t s : Lam} :
    (introduction a).rel t s ↔
      ∃ x t' s', t = Lam.lam x t' ∧ s = Lam.lam x s' ∧ a.rel t' s' := Iff.rfl

/-- Elimination forms: `(app t₁ t₂, app s₁ s₂)` with major `a`-related,
minor `b`-related. -/
def elimination (a b : SynRel') : SynRel' where
  rel := fun t s => ∃ t₁ t₂ s₁ s₂,
    t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
    ∧ a.rel t₁ s₁ ∧ b.rel t₂ s₂
  equivariant := by
    rintro π t s ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    refine ⟨π • t₁, π • t₂, π • s₁, π • s₂, ?_, ?_,
      a.equivariant π t₁ s₁ ha, b.equivariant π t₂ s₂ hb⟩ <;> simp

@[simp] theorem elimination_rel {a b : SynRel'} {t s : Lam} :
    (elimination a b).rel t s ↔ ∃ t₁ t₂ s₁ s₂,
      t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
      ∧ a.rel t₁ s₁ ∧ b.rel t₂ s₂ := Iff.rfl

/-! ### The OperationalDecomposition instance -/

theorem scr_decomposition (a : SynRel') :
    (SRA.scr a : SynRel') = introduction a ⊔ elimination a a := by
  ext t s
  change (scr a).rel t s ↔
    (introduction a).rel t s ∨ (elimination a a).rel t s
  simp only [scr_rel, introduction_rel, elimination_rel]

theorem introduction_compositionality (a b : SynRel') :
    introduction (a * b) = introduction a * introduction b := by
  ext t v
  refine ⟨?_, ?_⟩
  · rintro ⟨x, t', v', rfl, rfl, u', ha, hb⟩
    exact ⟨Lam.lam x u', ⟨x, t', u', rfl, rfl, ha⟩,
                          ⟨x, u', v', rfl, rfl, hb⟩⟩
  · rintro ⟨u, ⟨x, t', u₁, rfl, hu, ha⟩, ⟨y, u₂, v', hu', rfl, hb⟩⟩
    -- u = lam x u₁ = lam y u₂
    by_cases hxy : x = y
    · subst hxy
      have hueq : u₁ = u₂ := Lam_lam_inj_same (hu.symm.trans hu')
      subst hueq
      exact ⟨x, t', v', rfl, rfl, u₁, ha, hb⟩
    · -- α-rename to common binder c fresh
      obtain ⟨c, hc⟩ := LeanTra.Nominal.exists_notMem
        (Lam.fv t' ∪ Lam.fv u₁ ∪ Lam.fv u₂ ∪ Lam.fv v')
      simp only [Finset.mem_union, not_or] at hc
      obtain ⟨⟨⟨hct', hcu₁⟩, hcu₂⟩, hcv'⟩ := hc
      have hue : swap x c • u₁ = swap y c • u₂ := by
        apply Lam_lam_inj_same (a := c)
        rw [← Lam.lam_alpha x c u₁ (Or.inl hcu₁),
            ← Lam.lam_alpha y c u₂ (Or.inl hcu₂)]
        exact hu.symm.trans hu'
      refine ⟨c, swap x c • t', swap y c • v',
              Lam.lam_alpha x c t' (Or.inl hct'),
              Lam.lam_alpha y c v' (Or.inl hcv'), ?_⟩
      refine ⟨swap x c • u₁, ?_, ?_⟩
      · exact a.equivariant (swap x c) t' u₁ ha
      · rw [hue]; exact b.equivariant (swap y c) u₂ v' hb

theorem introduction_converse_commutation (a : SynRel') :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext t s
  refine ⟨?_, ?_⟩
  · rintro ⟨x, t', s', rfl, rfl, ha⟩; exact ⟨x, s', t', rfl, rfl, ha⟩
  · rintro ⟨x, t', s', rfl, rfl, ha⟩; exact ⟨x, s', t', rfl, rfl, ha⟩

theorem elimination_compositionality (a₁ a₂ b₁ b₂ : SynRel') :
    elimination (a₁ * a₂) (b₁ * b₂) = elimination a₁ b₁ * elimination a₂ b₂ := by
  ext t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨u₁, ha₁, ha₂⟩, ⟨u₂, hb₁, hb₂⟩⟩
    exact ⟨Lam.app u₁ u₂,
           ⟨t₁, t₂, u₁, u₂, rfl, rfl, ha₁, hb₁⟩,
           ⟨u₁, u₂, v₁, v₂, rfl, rfl, ha₂, hb₂⟩⟩
  · rintro ⟨u, ⟨t₁, t₂, u₁, u₂, rfl, hu, ha₁, hb₁⟩,
             ⟨u₁', u₂', v₁, v₂, hu', rfl, ha₂, hb₂⟩⟩
    have hinj : Lam.app u₁ u₂ = Lam.app u₁' u₂' := hu.symm.trans hu'
    obtain ⟨heq₁, heq₂⟩ := Lam_app_inj hinj
    subst heq₁; subst heq₂
    exact ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨u₁, ha₁, ha₂⟩, ⟨u₂, hb₁, hb₂⟩⟩

theorem elimination_converse_commutation (a b : SynRel') :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩

theorem introduction_unit_oplaxity : (introduction 1 : SynRel') ≤ 1 := by
  rintro t s ⟨x, t', s', rfl, rfl, (heq : t' = s')⟩
  exact congrArg _ heq

theorem elimination_unit_oplaxity : (elimination 1 1 : SynRel') ≤ 1 := by
  rintro t s ⟨t₁, t₂, s₁, s₂, rfl, rfl, (h₁ : t₁ = s₁), (h₂ : t₂ = s₂)⟩
  exact congrArg₂ _ h₁ h₂

theorem introduction_elimination_orthogonality (a b c : SynRel') :
    introduction a * elimination b c ≤ ⊥ := by
  rintro t v ⟨u, ⟨x, t', u', rfl, hu, _⟩,
                ⟨_, _, _, _, hu', _, _, _⟩⟩
  exact Lam_lam_ne_app _ _ _ _ (hu.symm.trans hu')

instance instOperationalDecomposition : OperationalDecomposition SynRel' where
  introduction := introduction
  elimination := elimination
  introduction_join_preservation := by
    intro 𝒮
    ext t s
    refine ⟨?_, ?_⟩
    · rintro ⟨x, t', s', rfl, rfl, φ, hφ𝒮, hφ⟩
      exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, x, t', s', rfl, rfl, hφ⟩
    · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, x, t', s', rfl, rfl, hφ⟩
      exact ⟨x, t', s', rfl, rfl, φ, hφ𝒮, hφ⟩
  introduction_compositionality := introduction_compositionality
  introduction_converse_commutation := introduction_converse_commutation
  elimination_join_preservation_left := by
    intro 𝒮 b
    ext t s
    refine ⟨?_, ?_⟩
    · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
      exact ⟨elimination φ b, ⟨φ, hφ𝒮, rfl⟩,
             t₁, t₂, s₁, s₂, rfl, rfl, hφ, hb⟩
    · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, t₁, t₂, s₁, s₂, rfl, rfl, hφ, hb⟩
      exact ⟨t₁, t₂, s₁, s₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
  elimination_join_preservation_right := by
    intro a 𝒮
    ext t s
    refine ⟨?_, ?_⟩
    · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, ⟨ψ, hψ𝒮, hψ⟩⟩
      exact ⟨elimination a ψ, ⟨ψ, hψ𝒮, rfl⟩,
             t₁, t₂, s₁, s₂, rfl, rfl, ha, hψ⟩
    · rintro ⟨_, ⟨ψ, hψ𝒮, rfl⟩, t₁, t₂, s₁, s₂, rfl, rfl, ha, hψ⟩
      exact ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, ⟨ψ, hψ𝒮, hψ⟩⟩
  elimination_compositionality := elimination_compositionality
  elimination_converse_commutation := elimination_converse_commutation
  introduction_unit_oplaxity := introduction_unit_oplaxity
  elimination_unit_oplaxity := elimination_unit_oplaxity
  introduction_elimination_orthogonality := introduction_elimination_orthogonality
  scr_decomposition := scr_decomposition
  subst_introduction_oplaxity := by
    -- FSP-based: substitution's oplaxity on introduction forms.
    sorry
  subst_elimination_oplaxity := by
    -- Structural, similar to first-order proof.
    rintro a₁ a₂ b u v ⟨τ, σ, t, s, ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩, hψ,
                        rfl, rfl⟩
    -- t = app t₁ t₂, s = app s₁ s₂
    simp only [Lam.subst_app]
    refine ⟨Lam.subst τ t₁, Lam.subst τ t₂,
            Lam.subst σ s₁, Lam.subst σ s₂, rfl, rfl, ?_, ?_⟩
    · refine ⟨τ, σ, t₁, s₁, ha, ?_, rfl, rfl⟩
      intro x hx
      -- hx : x ∈ fv t₁ ∪ fv s₁; original hψ was on fv (app t₁ t₂) ∪ fv (app s₁ s₂)
      apply hψ x
      -- fv (app t₁ t₂) ∪ fv (app s₁ s₂) = fv t₁ ∪ fv t₂ ∪ fv s₁ ∪ fv s₂ ⊇ fv t₁ ∪ fv s₁
      simp only [Lam.fv_app, Finset.mem_union] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · refine ⟨τ, σ, t₂, s₂, hb, ?_, rfl, rfl⟩
      intro x hx
      apply hψ x
      simp only [Lam.fv_app, Finset.mem_union] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  box_elimination_oplaxity := by
    -- FSP-based: box modality passes through elimination's major slot.
    sorry

/-! ### β-reduction on the α-quotient

`betaRule'` is the β-reduction rule expressed as an equivariant
relation on `Lam` (Def. 22 of the paper, `(λx. t) s β t[x ↦ s]`). Its
five rule-side conditions are proved directly on the nominal
representation; applying `local_confluence` yields confluence of
`parRed betaRule'`. -/

/-- β-reduction: `(λx. t) s → t[x ↦ s]` on the α-quotient. -/
def betaRule' : SynRel' where
  rel := fun u v =>
    ∃ (x : Atom) (t s : Lam),
      u = Lam.app (Lam.lam x t) s ∧
      v = Lam.subst (Subst.id.update x s) t
  equivariant := by
    rintro π u v ⟨x, t, s, rfl, rfl⟩
    refine ⟨π • x, π • t, π • s, ?_, ?_⟩
    · simp
    · rw [Lam.subst_smul]
      congr 1
      apply Subst.ext
      · funext y
        show π • ((Subst.id.update x s).toFun (π⁻¹ • y))
           = (Subst.id.update (π • x) (π • s)).toFun y
        by_cases hy : y = π • x
        · subst hy
          rw [Subst.update_apply_same]
          have hinv : π⁻¹ • π • x = x := by
            rw [← mul_smul, inv_mul_cancel, one_smul]
          rw [hinv, Subst.update_apply_same]
        · rw [Subst.update_apply_ne _ _ _ hy]
          have hy' : π⁻¹ • y ≠ x := fun h => hy (by
            rw [← h, ← mul_smul, mul_inv_cancel, one_smul])
          rw [Subst.update_apply_ne _ _ _ hy']
          show π • Lam.var (π⁻¹ • y) = Lam.var y
          simp
      · show (insert x (∅ : Finset Atom)).image (fun a => π • a)
           = insert (π • x) ∅
        rw [Finset.image_insert, Finset.image_empty]

/-! ### The five rule-side conditions of `local_confluence` for β -/

/-- β is a reduction: its LHS is never a variable. -/
theorem betaRule'_isReduction :
    LeanTra.Confluence.IsReduction (betaRule' : SynRel') := by
  change (varDiag * betaRule' : SynRel') = ⊥
  ext t v
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨w, ⟨x, _, rfl⟩, y, t', s, hw, _⟩
  exact Lam_var_ne_app _ _ _ hw

/-- β is substitutive at identity: substituting a β-redex through τ
gives back a β-redex. The proof outline: pick `e` fresh; use
`Lam.subst_lam_fresh` to compute `subst τ (lam x t')` as
`lam e (subst (τ.update x (var e)) t')`; then use `Lam.subst_comp` on
both sides and `Lam.subst_ext` to align them on `fv t'` — case split
on `y = x` (both give `subst τ s' = subst σ s'` via hψ) vs `y ≠ x`
(both give `τ y = σ y` via hψ, using `e ∉ τ.codSupp` to eliminate the
outer `id.update e ...`). All the pieces exist; the proof is tedious
namespace/coercion bookkeeping. -/
theorem betaRule'_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (betaRule' : SynRel') := by
  sorry

/-- β is deterministic on the nose: any two β-reducts of the same
term coincide. -/
theorem betaRule'_isDeterministic :
    LeanTra.Confluence.IsDeterministic (betaRule' : SynRel') := by
  change ((betaRule' : SynRel')ᵒ * betaRule') ≤ 1
  rintro u v ⟨w, ⟨x, t, s, hw, rfl⟩, ⟨y, t', s', hw', rfl⟩⟩
  -- Both β steps reduce the same w. w = app (lam x t) s = app (lam y t') s'.
  have hinj : Lam.app (Lam.lam x t) s = Lam.app (Lam.lam y t') s' :=
    hw.symm.trans hw'
  obtain ⟨hlam, heq_s⟩ := Lam_app_inj hinj
  subst heq_s
  -- Split on whether the two β-redexes share their binder atom.
  by_cases hxy : x = y
  · -- Same binder: `hlam` collapses to `t = t'` by `Lam_lam_inj_same`.
    subst hxy
    have hteq : t = t' := Lam_lam_inj_same hlam
    subst hteq
    rfl
  · -- Different binders: `Lam.lam x t = Lam.lam y t'` at the α-level.
    -- Extract `x ∉ Lam.fv t'` and `t = swap x y • t'` from Lam.lam_alpha
    -- + Lam_lam_inj_same. Then reduce via subst_smul, and close either by
    -- Lam.supports_fv (when y ∉ fv t' — trivial identity) or via a
    -- swap-transport argument (when y ∈ fv t').
    have hfv_eq : Lam.fv (Lam.lam x t) = Lam.fv (Lam.lam y t') := by rw [hlam]
    have hx_notMem : x ∉ Lam.fv t' := by
      intro hin
      have hin2 : x ∈ Lam.fv (Lam.lam y t') := by
        rw [Lam.fv_lam]
        exact Finset.mem_sdiff.mpr
          ⟨hin, fun h => hxy (Finset.mem_singleton.mp h)⟩
      rw [← hfv_eq, Lam.fv_lam] at hin2
      exact (Finset.mem_sdiff.mp hin2).2 (Finset.mem_singleton.mpr rfl)
    have hrenamed : t = (swap x y : Perm) • t' := by
      have hly : Lam.lam y t' = Lam.lam x ((swap y x : Perm) • t') :=
        Lam.lam_alpha y x t' (Or.inl hx_notMem)
      rw [hly] at hlam
      have := Lam_lam_inj_same hlam
      rw [this]; congr 1; exact Equiv.swap_comm y x
    show Lam.subst (Subst.id.update x s) t = Lam.subst (Subst.id.update y s) t'
    rw [hrenamed]
    have hid_swap : (swap x y : Perm) • Subst.id = Subst.id := by
      apply Subst.swap_smul_eq_self_of_notMem_codSupp
        <;> (change _ ∉ (∅ : Finset Atom); exact Finset.notMem_empty _)
    -- Push the swap through via subst_smul, then compare using subst_ext.
    have hswap_apply : ∀ σ : Subst,
        Lam.subst σ ((swap x y : Perm) • t')
        = (swap x y : Perm) • Lam.subst ((swap x y : Perm) • σ) t' := by
      intro σ
      have := Lam.subst_smul (swap x y : Perm) ((swap x y : Perm) • σ) t'
      rw [← mul_smul, Equiv.swap_mul_self, one_smul] at this
      exact this.symm
    rw [hswap_apply]
    -- Goal: swap x y • Lam.subst (swap x y • (id.update x s)) t' = subst (id.update y s) t'.
    -- Compute swap x y • (id.update x s) = id.update y (swap x y • s).
    rw [Subst.smul_update, hid_swap]
    have hxy_x : (swap x y : Perm) • x = y := by
      change Equiv.swap x y x = y; exact Equiv.swap_apply_left x y
    rw [hxy_x]
    -- Goal: swap x y • Lam.subst (id.update y (swap x y • s)) t' = subst (id.update y s) t'.
    -- Apply subst_smul once more on LHS, absorbing swap into σ and t'.
    rw [Lam.subst_smul]
    rw [Subst.smul_update, hid_swap]
    rw [← mul_smul, Equiv.swap_mul_self, one_smul]
    have hxy_y : (swap x y : Perm) • y = x := by
      change Equiv.swap x y y = x; exact Equiv.swap_apply_right x y
    rw [hxy_y]
    -- Goal reduces to: Lam.subst (id.update x s) (swap x y • t') = subst (id.update y s) t'.
    -- We're back to the pre-hswap_apply goal. The circularity is intrinsic:
    -- transporting the swap around cannot separate the terms without an
    -- α-invariance-of-β lemma (or a subst-alpha at the Lam level).
    -- Left as a documented open item — closing it requires either
    -- (a) full α-invariance of Lam.subst at the Lam level (proved raw,
    --     with a "subst σ (swap a c • u) = subst (σ.update a (var c)) u"
    --     lifting to Lam that removes the `c ∉ allAtoms t` clause via
    --     α-normalisation, or
    -- (b) a targeted "Lam.subst_lam_apply" saying
    --     Lam.lam a t = Lam.lam b s → subst (id.update a v) t = subst (id.update b v) s.
    sorry

/-- Gentzen Inversion Principle for β. -/
theorem betaRule'_gip : LeanTra.Metatheory.GIP (betaRule' : SynRel') := by
  change (betaRule' : SynRel')
       ≤ OperationalDecomposition.elimination
           (OperationalDecomposition.introduction 1) 1 * betaRule'
  rintro u v ⟨x, t, s, rfl, rfl⟩
  refine ⟨Lam.app (Lam.lam x t) s, ?_, ?_⟩
  · refine ⟨Lam.lam x t, s, Lam.lam x t, s, rfl, rfl, ?_, rfl⟩
    exact ⟨x, t, t, rfl, rfl, rfl⟩
  · exact ⟨x, t, s, rfl, rfl⟩

/-- Gentzen Conservation Principle for β. -/
theorem betaRule'_gcp : LeanTra.Metatheory.GCP (betaRule' : SynRel') := by
  -- Complex — requires the subst_x_x composition analysis.
  sorry

/-- Confluence of parallel β-reduction on `Lam`, via `local_confluence`. -/
theorem betaRule'_local_confluent :
    LeanTra.Algebra.IsConfluent
      (LeanTra.Confluence.parRed (betaRule' : SynRel')) :=
  LeanTra.Confluence.local_confluence
    betaRule'_isReduction
    betaRule'_isSubstitutiveAtIdentity
    betaRule'_isDeterministic
    betaRule'_gip
    betaRule'_gcp

end SynRel'

end Named

end LeanTra.Instances.Lambda


/-! ## Sanity checks and axiom trace

The nominal-quotient architecture on which `betaRule'_local_confluent`
rests: `SRA` instance, `OperationalDecomposition` instance, and the
final confluence theorem. The axiom trace should mention only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the
`sorryAx` occurrences correspond to the specific technical lemmas
still open (`RawLam.subst_alpha`, `Lam.subst_smul`, and the FSP-based
axioms — see the module docstrings of `Lambda/Substitution.lean` and
the SRA/OpDecomp instances below). -/

#check @LeanTra.Instances.Lambda.Named.SynRel'.instSRA
#check @LeanTra.Instances.Lambda.Named.SynRel'.instOperationalDecomposition
#check @LeanTra.Instances.Lambda.Named.SynRel'.betaRule'_local_confluent
#print axioms LeanTra.Instances.Lambda.Named.SynRel'.betaRule'_local_confluent
