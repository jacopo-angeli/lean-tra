/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Nominal.Basic

/-!
# λ-calculus syntax as a nominal α-quotient

The second-order syntax of Gavazzo's LICS'26 (Def. 10, 12, 13),
specialised to the λ-signature `{lam : (1), app : (0,0)}`.

## Contents

* `RawLam` — the raw named terms `𝒯Σ(V)`.
* `RawLam.act` and `MulAction Perm RawLam` — the structural
  permutation action of Def. 13.
* `RawLam.fv` — free variables, equivariant.
* `RawLam.allAtoms` — all atoms occurring (support of the raw term).
* `AlphaEq` — α-equivalence, cofinite definition, equivalence relation.
* `RawLam.smul_swap`, `AlphaEq.smul` — swap conjugation and
  equivariance of α.
* `Lam := Quotient RawLam.instSetoid` — the α-quotient `𝒯Σᵅ(V)`.
* Constructors `Lam.var`, `Lam.app`, `Lam.lam`, `MulAction Perm Lam`,
  `Lam.fv`, `Lam.fv_smul`.
* The α-swap identity `Lam.lam a u = Lam.lam b (swap a b • u)` for
  `b # u`.
* Finite support of every `Lam` value via its free variables.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. Def. 10 (raw terms), Def. 12 (α-quotient), Def. 13
  (permutation action).
* Aydemir, Charguéraud, Pierce, Pollack, Weirich. *Engineering formal
  metatheory.* POPL 2008 (cofinite α).
-/
@[expose] public section

namespace LeanTra.Instances.Lambda

/-! ## Section 1' — Named raw terms, permutation action, free variables

Rebuild of the term layer using the paper's second-order syntax
(§3.1.2): variables are *atoms* with names, binders carry an explicit
atom, and permutations act structurally. Everything new lives under the
namespace `Named` so it can coexist with the existing well-scoped
`Lam n` while Sections 1'–3' are being staged. Once Section 3' is
stable and every axiom is proved, the old material is deleted and the
`Named` namespace is opened at the outer level.

The nominal machinery of Section 0 (`Perm`, `Nominal.IsNominal`,
`Nominal.Supports`, freshness) is used *only* through its abstract API
here — the concrete `MulAction` on `RawLam` is defined structurally,
and the resulting nominal-set structure follows from the general
instances. -/

namespace Named

open LeanTra.Nominal

/-- Raw λ-terms with named variables — the paper's `𝒯Σ(V)` for the
signature `Σ = { lam : (1), app : (0,0) }`. Binders carry the atom they
bind; α-equivalence is defined separately below and quotient-ed out to
recover `𝒯Σᵅ(V)`. -/
inductive RawLam : Type where
  /-- A variable, given by its atom. -/
  | var : Atom → RawLam
  /-- Application. -/
  | app : RawLam → RawLam → RawLam
  /-- Abstraction over a named atom. -/
  | lam : Atom → RawLam → RawLam
  deriving DecidableEq

namespace RawLam

/-! ### Permutation action

`Perm` acts on raw terms by renaming every atom occurrence — both free
variables *and* binders. This is the structural action Def. 13 of the
paper describes, before α-quotienting. -/

/-- Structural action of a permutation on a raw term. -/
def act : Perm → RawLam → RawLam
  | π, var a     => var (π a)
  | π, app t s   => app (act π t) (act π s)
  | π, lam a t   => lam (π a) (act π t)

theorem act_one (t : RawLam) : act 1 t = t := by
  induction t with
  | var a       => rfl
  | app t s iht ihs => simp [act, iht, ihs]
  | lam a t ih  => simp [act, ih]

theorem act_mul (π₁ π₂ : Perm) (t : RawLam) :
    act (π₁ * π₂) t = act π₁ (act π₂ t) := by
  induction t with
  | var a       =>
      show var ((π₁ * π₂) a) = var (π₁ (π₂ a))
      rfl
  | app t s iht ihs => simp [act, iht, ihs]
  | lam a t ih  =>
      show lam ((π₁ * π₂) a) (act (π₁ * π₂) t)
         = lam (π₁ (π₂ a)) (act π₁ (act π₂ t))
      rw [ih]; rfl

instance instMulAction : MulAction Perm RawLam where
  smul     := act
  one_smul := act_one
  mul_smul := act_mul

instance : IsNominal RawLam where

/-! ### Simp shapes for the action -/

@[simp] theorem smul_var (π : Perm) (a : Atom) :
    π • (var a) = var (π a) := rfl

@[simp] theorem smul_app (π : Perm) (t s : RawLam) :
    π • (app t s) = app (π • t) (π • s) := rfl

@[simp] theorem smul_lam (π : Perm) (a : Atom) (t : RawLam) :
    π • (lam a t) = lam (π a) (π • t) := rfl

/-! ### Free variables

`fv t` is the finite set of atoms occurring free in `t`. It will serve
as a canonical *support* for `t` (proved in Batch B). Its equivariance
under the action is the first non-trivial property of the nominal
layer. -/

/-- Set of free variables of a raw term. -/
def fv : RawLam → Finset Atom
  | var a     => {a}
  | app t s   => fv t ∪ fv s
  | lam a t   => fv t \ {a}

@[simp] theorem fv_var (a : Atom) : fv (var a) = {a} := rfl
@[simp] theorem fv_app (t s : RawLam) : fv (app t s) = fv t ∪ fv s := rfl
@[simp] theorem fv_lam (a : Atom) (t : RawLam) : fv (lam a t) = fv t \ {a} := rfl

/-- The action of `Perm` on the *finite-set-of-atoms* level is the
image; `fv` commutes with the action, i.e. `fv (π • t) = π • fv t`.
This is the equivariance of `fv` as a map `RawLam → Finset Atom`. -/
theorem fv_smul (π : Perm) (t : RawLam) :
    fv (π • t) = (fv t).image (fun a => π • a) := by
  induction t with
  | var a       =>
      show ({π a} : Finset Atom) = ({a} : Finset Atom).image (fun x => π • x)
      rw [Finset.image_singleton]
      rfl
  | app t s iht ihs =>
      show fv (π • t) ∪ fv (π • s)
         = (fv t ∪ fv s).image (fun a => π • a)
      rw [iht, ihs, Finset.image_union]
  | lam a t ih  =>
      show fv (π • t) \ {π a}
         = ((fv t) \ {a}).image (fun x => π • x)
      rw [ih]
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hne⟩
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        intro h; subst h
        exact hne rfl
      · rintro ⟨x, ⟨hx, hne⟩, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ?_⟩
        intro h
        apply hne
        exact (Equiv.injective π) h

/-! ### Support and finite support

For a *raw* term, the natural support is the set of atoms occurring
anywhere — free variables and binders alike — because permuting a
binder changes the raw term (α-equivalence is not yet in play). Once
we quotient by α, the support collapses to `fv`. -/

/-- All atoms occurring in a raw term, free or bound. -/
def allAtoms : RawLam → Finset Atom
  | var a     => {a}
  | app t s   => allAtoms t ∪ allAtoms s
  | lam a t   => insert a (allAtoms t)

@[simp] theorem allAtoms_var (a : Atom) : allAtoms (var a) = {a} := rfl
@[simp] theorem allAtoms_app (t s : RawLam) :
    allAtoms (app t s) = allAtoms t ∪ allAtoms s := rfl
@[simp] theorem allAtoms_lam (a : Atom) (t : RawLam) :
    allAtoms (lam a t) = insert a (allAtoms t) := rfl

theorem fv_subset_allAtoms (t : RawLam) : fv t ⊆ allAtoms t := by
  induction t with
  | var a       => intro b hb; exact hb
  | app t s iht ihs =>
      intro b hb
      rcases Finset.mem_union.mp hb with h | h
      · exact Finset.mem_union_left _ (iht h)
      · exact Finset.mem_union_right _ (ihs h)
  | lam a t ih  =>
      intro b hb
      have hb' : b ∈ fv t := (Finset.mem_sdiff.mp hb).1
      exact Finset.mem_insert_of_mem (ih hb')

/-- `allAtoms t` supports `t`: a permutation fixing every atom of `t`
(free or bound) is the identity on `t`. -/
theorem supports_allAtoms (t : RawLam) : Supports (allAtoms t) t := by
  intro π hπ
  induction t with
  | var a       =>
      show var (π • a) = var a
      rw [hπ a (Finset.mem_singleton.mpr rfl)]
  | app t s iht ihs =>
      show app (π • t) (π • s) = app t s
      have ht : π • t = t := iht (fun b hb =>
        hπ b (Finset.mem_union_left _ hb))
      have hs : π • s = s := ihs (fun b hb =>
        hπ b (Finset.mem_union_right _ hb))
      rw [ht, hs]
  | lam a t ih  =>
      show lam (π • a) (π • t) = lam a t
      have ha : π • a = a := hπ a (Finset.mem_insert_self a _)
      have ht : π • t = t := ih (fun b hb =>
        hπ b (Finset.mem_insert_of_mem hb))
      rw [ha, ht]

/-- Every raw term is finitely supported (by its `allAtoms`). -/
theorem finitelySupported (t : RawLam) : FinitelySupported t :=
  ⟨allAtoms t, supports_allAtoms t⟩

end RawLam

/-! ### α-equivalence — cofinite formulation

Two raw terms are α-equivalent when they differ only by the choice of
bound-variable names. We use the *cofinite* formulation (Aydemir /
Charguéraud style): `lam a t ∼α lam b s` iff for all atoms `c` outside
some finite set `L`, swapping in `c` yields α-equivalent bodies. The
`L` acts as a placeholder for "any name fresh enough", making
reflexivity, symmetry, and transitivity all provable by structural
induction on the derivation without existential shuffling. -/

inductive AlphaEq : RawLam → RawLam → Prop
  | var (a : Atom) : AlphaEq (RawLam.var a) (RawLam.var a)
  | app {t₁ s₁ t₂ s₂ : RawLam}
        (h₁ : AlphaEq t₁ s₁) (h₂ : AlphaEq t₂ s₂) :
        AlphaEq (RawLam.app t₁ t₂) (RawLam.app s₁ s₂)
  | lam (a b : Atom) (t s : RawLam) (L : Finset Atom)
        (h : ∀ c, c ∉ L →
             AlphaEq ((swap a c) • t) ((swap b c) • s)) :
        AlphaEq (RawLam.lam a t) (RawLam.lam b s)

namespace AlphaEq

/-! ### Reflexivity

Strengthened to `∀ π, AlphaEq (π • t) (π • t)` so the `lam` case can
re-instantiate the induction hypothesis at `swap a c * π`. Plain
reflexivity is then the specialisation to `π = 1`. -/

theorem refl_smul (t : RawLam) : ∀ π : Perm, AlphaEq (π • t) (π • t) := by
  induction t with
  | var a =>
      intro π
      exact AlphaEq.var (π • a)
  | app t s iht ihs =>
      intro π
      exact AlphaEq.app (iht π) (ihs π)
  | lam a t ih =>
      intro π
      refine AlphaEq.lam (π • a) (π • a) (π • t) (π • t) ∅ ?_
      intro c _
      have h := ih (swap (π • a) c * π)
      rwa [mul_smul] at h

theorem refl (t : RawLam) : AlphaEq t t := by
  have h := refl_smul t 1
  rwa [one_smul] at h

/-! ### Symmetry

Straightforward — `AlphaEq` is symmetric constructor-by-constructor,
and the cofinite `lam` case swaps `(a, b)` in the conclusion. -/

theorem symm : ∀ {t s : RawLam}, AlphaEq t s → AlphaEq s t := by
  intro t s h
  induction h with
  | var a => exact AlphaEq.var a
  | app _ _ iht ihs => exact AlphaEq.app iht ihs
  | lam a b t s L _ ih =>
      exact AlphaEq.lam b a s t L (fun c hc => ih c hc)

/-! ### Transitivity

By induction on the first derivation with the second endpoint left
inside the motive (`∀ u, AlphaEq s u → AlphaEq t u`) so the IH for the
`lam` case can be re-instantiated at the fresh atom's target. The `lam`
case unions the two cofinite bounds. -/

theorem trans_aux : ∀ {t s : RawLam}, AlphaEq t s →
    ∀ u, AlphaEq s u → AlphaEq t u := by
  intro t s h₁
  induction h₁ with
  | var a =>
      intro u h₂; exact h₂
  | @app t₁ s₁ t₂ s₂ _ _ iht ihs =>
      intro u h₂
      cases h₂ with
      | app h₁' h₂' => exact AlphaEq.app (iht _ h₁') (ihs _ h₂')
  | @lam a b t s L _ ih =>
      intro u h₂
      cases h₂ with
      | @lam _ c _ u' L' h' =>
          refine AlphaEq.lam a c t u' (L ∪ L') ?_
          intro d hd
          have hdL  : d ∉ L  := fun h => hd (Finset.mem_union.mpr (Or.inl h))
          have hdL' : d ∉ L' := fun h => hd (Finset.mem_union.mpr (Or.inr h))
          exact ih d hdL _ (h' d hdL')

theorem trans {t s u : RawLam}
    (h₁ : AlphaEq t s) (h₂ : AlphaEq s u) : AlphaEq t u :=
  trans_aux h₁ u h₂

/-! ### Setoid -/

theorem equivalence : Equivalence AlphaEq :=
  ⟨refl, symm, trans⟩

end AlphaEq

/-- The α-equivalence setoid on `RawLam`. -/
instance RawLam.instSetoid : Setoid RawLam :=
  ⟨AlphaEq, AlphaEq.equivalence⟩

/-! ### Equivariance of α

Mathlib supplies the group-theoretic identity we need in the form
`Equiv.swap_apply_apply : swap (π a) (π b) = π * swap a b * π⁻¹`.
Lifting it to raw terms via `mul_smul` gives the fact that `π` moves
past `swap` at the term level, with binder atoms conjugated. -/

/-- Swap moves past `π` in the raw-term action, with atoms conjugated. -/
theorem RawLam.smul_swap (π : Perm) (a b : Atom) (t : RawLam) :
    π • ((swap a b) • t) = (swap (π • a) (π • b)) • (π • t) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  show π * Equiv.swap a b = Equiv.swap (π • a) (π • b) * π
  have h : Equiv.swap (π • a) (π • b) = π * Equiv.swap a b * π⁻¹ :=
    Equiv.swap_apply_apply π a b
  rw [h, mul_assoc, inv_mul_cancel, mul_one]

/-- `AlphaEq` is preserved by the action of `Perm`. -/
theorem AlphaEq.smul (π : Perm) : ∀ {t s : RawLam},
    AlphaEq t s → AlphaEq (π • t) (π • s) := by
  intro t s h
  induction h with
  | var a => exact AlphaEq.var (π • a)
  | app _ _ iht ihs => exact AlphaEq.app iht ihs
  | @lam a b t s L _ ih =>
      -- Goal: AlphaEq (π • lam a t) (π • lam b s)
      --     = AlphaEq (lam (π • a) (π • t)) (lam (π • b) (π • s))
      refine AlphaEq.lam (π • a) (π • b) (π • t) (π • s)
        (L.image (fun x => π • x)) ?_
      intro c hc
      -- c ∉ π • L means π⁻¹ • c ∉ L
      have hcL : π⁻¹ • c ∉ L := by
        intro hin
        apply hc
        rw [Finset.mem_image]
        refine ⟨π⁻¹ • c, hin, ?_⟩
        rw [← mul_smul, mul_inv_cancel, one_smul]
      -- IH at π⁻¹ • c: AlphaEq (π • swap a (π⁻¹ • c) • t) (π • swap b (π⁻¹ • c) • s)
      have hIH := ih (π⁻¹ • c) hcL
      -- Move π past the swaps using RawLam.smul_swap
      rw [RawLam.smul_swap, RawLam.smul_swap] at hIH
      -- Now the atoms are swap (π • a) (π • π⁻¹ • c) and swap (π • b) (π • π⁻¹ • c)
      -- Which simplify to swap (π • a) c and swap (π • b) c
      have hcanc : π • π⁻¹ • c = c := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      rw [hcanc] at hIH
      exact hIH

/-! ### The quotient `Lam := 𝒯Σᵅ(V)`

The α-equivalence quotient of raw terms is the paper's `𝒯Σᵅ(V)`. Every
operation defined on `RawLam` that respects `AlphaEq` lifts uniquely to
`Lam`. We build the `MulAction` and `IsNominal` structure on `Lam` by
lifting from `RawLam`. -/

/-- The α-equivalence quotient of raw terms — the second-order syntax
of the paper (Def. 12). -/
def Lam : Type := Quotient RawLam.instSetoid

namespace Lam

/-- The canonical projection `RawLam → Lam`. -/
def mk (t : RawLam) : Lam := Quotient.mk _ t

instance : Coe RawLam Lam := ⟨mk⟩

/-- Variables. -/
def var (a : Atom) : Lam := mk (RawLam.var a)

/-- Application, lifted through α. -/
def app : Lam → Lam → Lam :=
  Quotient.lift₂ (fun t s => mk (RawLam.app t s))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (AlphaEq.app h₁ h₂))

/-- Abstraction, lifted through α at fixed binder atom. -/
def lam (a : Atom) : Lam → Lam :=
  Quotient.lift (fun t => mk (RawLam.lam a t))
    (fun _ _ h => Quotient.sound
      (AlphaEq.lam a a _ _ ∅ (fun c _ => AlphaEq.smul (swap a c) h)))

@[simp] theorem app_mk (t s : RawLam) :
    app (mk t) (mk s) = mk (RawLam.app t s) := rfl

@[simp] theorem lam_mk (a : Atom) (t : RawLam) :
    lam a (mk t) = mk (RawLam.lam a t) := rfl

/-! ### `Perm` action on `Lam` -/

/-- Action of `Perm` on `Lam`, lifted through α from `RawLam`. -/
instance instMulAction : MulAction Perm Lam where
  smul π := Quotient.lift (fun t => mk (π • t))
    (fun _ _ h => Quotient.sound (AlphaEq.smul π h))
  one_smul t := by
    refine Quotient.inductionOn t ?_
    intro t
    show mk ((1 : Perm) • t) = mk t
    rw [one_smul]
  mul_smul π₁ π₂ t := by
    refine Quotient.inductionOn t ?_
    intro t
    show mk ((π₁ * π₂) • t) = mk (π₁ • (π₂ • t))
    rw [mul_smul]

instance : IsNominal Lam where

@[simp] theorem smul_mk (π : Perm) (t : RawLam) :
    π • (mk t) = mk (π • t) := rfl

@[simp] theorem smul_var (π : Perm) (a : Atom) :
    π • (var a) = var (π • a) := rfl

@[simp] theorem smul_app (π : Perm) (u v : Lam) :
    π • (app u v) = app (π • u) (π • v) := by
  refine Quotient.inductionOn₂ u v ?_
  intro t s
  rfl

@[simp] theorem smul_lam (π : Perm) (a : Atom) (u : Lam) :
    π • (lam a u) = lam (π • a) (π • u) := by
  refine Quotient.inductionOn u ?_
  intro t
  rfl

/-! ### Free variables on the quotient

`fv` on `RawLam` is α-invariant (proved below), so it descends to a
map `Lam → Finset Atom`. That set is the paper's support of the
α-equivalence class. -/

/-- Auxiliary set-level identity: for `c ∉ S`, applying `swap a c`
pointwise and then removing `c` gives back `S \ {a}`. Two cases: if
`a ∈ S` then swap sends `a ↦ c` and everything else to itself, so
image = (S \ {a}) ∪ {c}, and removing `c` gets S \ {a}. If `a ∉ S`
then swap fixes S, image = S, and removing c (which isn't in S) gets
S = S \ {a}. -/
theorem image_swap_sdiff (S : Finset Atom) (a c : Atom) (hc : c ∉ S) :
    S.image (fun x => swap a c • x) \ {c} = S \ {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨y, hyS, hyx⟩, hxc⟩
    -- swap a c • y = x, x ≠ c. Reconstruct y as swap a c • x.
    have hy : y = swap a c • x := by
      have hcongr : swap a c • (swap a c • y) = swap a c • x :=
        congrArg (swap a c • ·) hyx
      rw [← mul_smul, Equiv.swap_mul_self, one_smul] at hcongr
      exact hcongr
    by_cases hxa : x = a
    · -- x = a case: y = swap a c • a = c, contradicting c ∉ S.
      have hy_eq_c : y = c := by
        rw [hy, hxa]
        show Equiv.swap a c a = c
        exact Equiv.swap_apply_left a c
      exact absurd (hy_eq_c ▸ hyS) hc
    · -- x ≠ a, x ≠ c, so swap a c fixes x, so y = x.
      have hyx' : y = x := by
        rw [hy]
        show Equiv.swap a c x = x
        exact Equiv.swap_apply_of_ne_of_ne hxa hxc
      exact ⟨hyx' ▸ hyS, hxa⟩
  · rintro ⟨hxS, hxa⟩
    -- x ∈ S, x ≠ a. Show x ∈ image ∧ x ≠ c.
    have hxc : x ≠ c := fun h => hc (h ▸ hxS)
    refine ⟨⟨x, hxS, ?_⟩, hxc⟩
    show Equiv.swap a c x = x
    exact Equiv.swap_apply_of_ne_of_ne hxa hxc

/-- Free variables are α-invariant. -/
theorem RawLam.fv_alphaEq : ∀ {t s : RawLam}, AlphaEq t s →
    RawLam.fv t = RawLam.fv s := by
  intro t s h
  induction h with
  | var a => rfl
  | app _ _ iht ihs => simp [RawLam.fv, iht, ihs]
  | @lam a b t s L _ ih =>
      -- Pick c fresh for L, fv t, fv s.
      obtain ⟨c, hc⟩ := LeanTra.Nominal.exists_notMem
        (L ∪ RawLam.fv t ∪ RawLam.fv s)
      have hcL : c ∉ L := fun h => hc
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h))))
      have hct : c ∉ RawLam.fv t := fun h => hc
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
      have hcs : c ∉ RawLam.fv s := fun h => hc
        (Finset.mem_union.mpr (Or.inr h))
      have hIH := ih c hcL
      -- hIH : fv (swap a c • t) = fv (swap b c • s), i.e.
      --      (fv t).image (swap a c) = (fv s).image (swap b c)
      rw [RawLam.fv_smul, RawLam.fv_smul] at hIH
      show RawLam.fv t \ {a} = RawLam.fv s \ {b}
      have h₁ := image_swap_sdiff (RawLam.fv t) a c hct
      have h₂ := image_swap_sdiff (RawLam.fv s) b c hcs
      calc RawLam.fv t \ {a}
          = (RawLam.fv t).image (fun x => swap a c • x) \ {c} := h₁.symm
        _ = (RawLam.fv s).image (fun x => swap b c • x) \ {c} := by rw [hIH]
        _ = RawLam.fv s \ {b} := h₂

/-- `fv` lifted to the α-quotient. -/
def fv : Lam → Finset Atom :=
  Quotient.lift RawLam.fv (fun _ _ h => RawLam.fv_alphaEq h)

@[simp] theorem fv_mk (t : RawLam) : fv (mk t) = RawLam.fv t := rfl
@[simp] theorem fv_var (a : Atom) : fv (var a) = {a} := rfl
@[simp] theorem fv_app (u v : Lam) : fv (app u v) = fv u ∪ fv v := by
  refine Quotient.inductionOn₂ u v ?_
  intro _ _
  rfl
@[simp] theorem fv_lam (a : Atom) (u : Lam) : fv (lam a u) = fv u \ {a} := by
  refine Quotient.inductionOn u ?_
  intro _
  rfl

end Lam

/-! ### The α-renaming lemma

Two permutations that agree on `fv t` produce α-equivalent results
when applied to `t`. This is the generic renaming lemma from which
the specific α-swap identity `lam a t = lam b (swap a b • t)` (for
`b # t`) follows. -/

/-- Permutations agreeing on `fv t` produce α-equivalent images. -/
theorem RawLam.smul_alpha_agree :
    ∀ (t : RawLam) (π₁ π₂ : Perm),
      (∀ x ∈ RawLam.fv t, π₁ x = π₂ x) →
      AlphaEq (π₁ • t) (π₂ • t) := by
  intro t
  induction t with
  | var x =>
      intro π₁ π₂ h
      have hxπ := h x (Finset.mem_singleton.mpr rfl)
      show AlphaEq (RawLam.var (π₁ • x)) (RawLam.var (π₂ • x))
      change AlphaEq (RawLam.var (π₁ x)) (RawLam.var (π₂ x))
      rw [hxπ]
      exact AlphaEq.var _
  | app t s iht ihs =>
      intro π₁ π₂ h
      have ht : ∀ x ∈ RawLam.fv t, π₁ x = π₂ x :=
        fun x hx => h x (Finset.mem_union_left _ hx)
      have hs : ∀ x ∈ RawLam.fv s, π₁ x = π₂ x :=
        fun x hx => h x (Finset.mem_union_right _ hx)
      exact AlphaEq.app (iht π₁ π₂ ht) (ihs π₁ π₂ hs)
  | lam d t' ih =>
      intro π₁ π₂ h
      show AlphaEq (RawLam.lam (π₁ • d) (π₁ • t'))
                   (RawLam.lam (π₂ • d) (π₂ • t'))
      refine AlphaEq.lam (π₁ • d) (π₂ • d) (π₁ • t') (π₂ • t')
        ((RawLam.fv t').image π₁ ∪ (RawLam.fv t').image π₂
          ∪ {π₁ • d, π₂ • d}) ?_
      intro c hc
      -- Convert `swap _ c • π_i • t'` to `(swap _ c * π_i) • t'`
      rw [← mul_smul, ← mul_smul]
      apply ih
      intro x hx
      -- Show (swap (π₁ • d) c * π₁) x = (swap (π₂ • d) c * π₂) x
      show swap (π₁ • d) c (π₁ x) = swap (π₂ • d) c (π₂ x)
      change Equiv.swap (π₁ d) c (π₁ x) = Equiv.swap (π₂ d) c (π₂ x)
      by_cases hxd : x = d
      · subst hxd
        rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
      · have hxfv : x ∈ RawLam.fv t' \ {d} :=
          Finset.mem_sdiff.mpr ⟨hx,
            fun heq => hxd (Finset.mem_singleton.mp heq)⟩
        have hpi : π₁ x = π₂ x := h x hxfv
        have hcne1 : c ∉ (RawLam.fv t').image π₁ := fun himg =>
          hc (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl himg))))
        have hcne2 : c ∉ (RawLam.fv t').image π₂ := fun himg =>
          hc (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr himg))))
        have hπ₁x_ne_c : π₁ x ≠ c := fun heq =>
          hcne1 (Finset.mem_image.mpr ⟨x, hx, heq⟩)
        have hπ₂x_ne_c : π₂ x ≠ c := fun heq =>
          hcne2 (Finset.mem_image.mpr ⟨x, hx, heq⟩)
        have hπ₁x_ne_π₁d : π₁ x ≠ π₁ d := fun heq =>
          hxd (Equiv.injective π₁ heq)
        have hπ₂x_ne_π₂d : π₂ x ≠ π₂ d := fun heq =>
          hxd (Equiv.injective π₂ heq)
        rw [Equiv.swap_apply_of_ne_of_ne hπ₁x_ne_π₁d hπ₁x_ne_c,
            Equiv.swap_apply_of_ne_of_ne hπ₂x_ne_π₂d hπ₂x_ne_c,
            hpi]

/-- **The α-swap identity.** For `b # t`, `lam a t` and `lam b (swap a b • t)`
are α-equivalent as raw terms. This is the primitive used to open a
`lam` with a bound name fresh for whatever data the surrounding
argument needs. -/
theorem RawLam.lam_alpha_swap (a b : Atom) (t : RawLam)
    (hb : b ∉ RawLam.fv t) :
    AlphaEq (RawLam.lam a t) (RawLam.lam b (swap a b • t)) := by
  by_cases hab : a = b
  · subst hab
    show AlphaEq (RawLam.lam a t) (RawLam.lam a (swap a a • t))
    have hself : (swap a a : Perm) = 1 := Equiv.swap_self a
    rw [hself, one_smul]
    exact AlphaEq.refl _
  · refine AlphaEq.lam a b t (swap a b • t)
      (insert a (insert b (RawLam.fv t))) ?_
    intro c hc
    have hca : c ≠ a := fun h => hc (h ▸ Finset.mem_insert_self _ _)
    have hcb : c ≠ b := fun h => hc (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hcfv : c ∉ RawLam.fv t := fun h => hc
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [← mul_smul]
    apply RawLam.smul_alpha_agree
    intro x hx
    show Equiv.swap a c x = (Equiv.swap b c * Equiv.swap a b) x
    rw [Equiv.Perm.mul_apply]
    have hxb : x ≠ b := fun h => hb (h ▸ hx)
    have hxc : x ≠ c := fun h => hcfv (h ▸ hx)
    by_cases hxa : x = a
    · -- x = a: swap a c a = c; swap a b a = b, swap b c b = c.
      subst hxa
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left,
          Equiv.swap_apply_left]
    · -- x ≠ a, x ≠ b, x ≠ c: both sides equal x.
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxc,
          Equiv.swap_apply_of_ne_of_ne hxa hxb,
          Equiv.swap_apply_of_ne_of_ne hxb hxc]

/-- Corresponding Lam-level identity. -/
theorem Lam.lam_alpha (a b : Atom) (u : Lam) (hb : b ∉ Lam.fv u ∨ b = a) :
    Lam.lam a u = Lam.lam b (swap a b • u) := by
  revert hb
  refine Quotient.inductionOn u ?_
  intro t hb
  rcases hb with hb | hab
  · show Lam.mk (RawLam.lam a t) = Lam.mk (RawLam.lam b (swap a b • t))
    exact Quotient.sound (RawLam.lam_alpha_swap a b t hb)
  · rw [hab]
    show Lam.mk (RawLam.lam a t) = Lam.mk (RawLam.lam a (swap a a • t))
    have hself : (swap a a : Perm) = 1 := Equiv.swap_self a
    rw [hself, one_smul]

/-- `fv` supports the term at the Lam level. -/
theorem Lam.supports_fv (u : Lam) : Supports (Lam.fv u) u := by
  refine Quotient.inductionOn u ?_
  intro t π hπ
  show Lam.mk (π • t) = Lam.mk t
  -- Show AlphaEq (π • t) t. It suffices that π agrees with 1 on fv t.
  apply Quotient.sound
  have : AlphaEq (π • t) ((1 : Perm) • t) := by
    apply RawLam.smul_alpha_agree
    intro x hx
    show π x = (1 : Perm) x
    change π • x = x
    exact hπ x hx
  rwa [one_smul] at this

theorem Lam.finitelySupported (u : Lam) : FinitelySupported u :=
  ⟨Lam.fv u, Lam.supports_fv u⟩

/-- Equivariance of `fv` at the `Lam` level, lifted from `RawLam.fv_smul`. -/
theorem Lam.fv_smul (π : Perm) (u : Lam) :
    Lam.fv (π • u) = (Lam.fv u).image (fun a => π • a) := by
  refine Quotient.inductionOn u ?_
  intro t
  show Lam.fv (Lam.mk (π • t)) = (Lam.fv (Lam.mk t)).image (fun a => π • a)
  simp only [Lam.fv_mk]
  exact RawLam.fv_smul π t

end Named

end LeanTra.Instances.Lambda
