/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Instances.SecondOrder.Lambda.Syntax

/-!
# Capture-avoiding substitution on the α-quotient

Following Def. 12 of Gavazzo's LICS'26 paper: a substitution is a map
`Atom → Lam` with finite support. We bundle the finite-support witness
into a structure `Subst` so that the support (and its derived codomain
support) are always accessible in proofs — especially in the FSP-based
arguments where the `lam` case needs a fresh atom outside the
substitution's codomain support.

## Contents

* `Subst` — the finite-support substitution structure.
* `Subst.id`, `Subst.update` — trivial and extension operations.
* `Subst.codSupp`, `Subst.freshAtom` — codomain support and the
  fresh-atom-picking primitive.
* `Subst.instMulAction`, `Subst.smul_apply` — `Perm` action on
  substitutions.
* `RawLam.subst` — structural definition of capture-avoiding
  substitution on the raw term, producing a `Lam` (α-quotient) value.
* `RawLam.subst_perm` — raw-level equivariance of `subst`, proved by
  structural induction using the bridging lemma
  `subst_lam_freshBinder_of_perm`.
* `RawLam.subst_swap` — the swap-substitution commutation identity,
  used to reduce `subst σ (swap a c • t)` to `subst (σ[a ↦ var c]) t`.
* `RawLam.subst_alpha` — α-invariance of `RawLam.subst`, proved by
  induction on the derivation of `AlphaEq`, bridging fresh binder
  atoms via `subst_lam_freshBinder` and reducing to the swap form via
  `subst_swap`.
* `Lam.subst` — the operation lifted to the α-quotient via
  `Quotient.lift`.
* `Lam.subst_smul` — equivariance of `Lam.subst`, an immediate
  consequence of `subst_perm` via `Quotient.inductionOn`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. Def. 12 (substitutions with finite support).
-/
@[expose] public section

namespace LeanTra.Instances.Lambda

namespace Named

open LeanTra.Nominal

/-- A **substitution**: a function `Atom → Lam` acting as identity
outside a finite set `supp`. This bundles the paper's "finitely
supported map from atoms to terms" (Def. 12). The `outside_id`
invariant makes `supp` a genuine support: whatever is outside is fixed
to `var x`, so `supp` upper-bounds the atoms the substitution actually
touches. -/
@[ext] structure Subst where
  /-- The underlying function. -/
  toFun : Atom → Lam
  /-- Atoms where the substitution differs from `var`. -/
  supp : Finset Atom
  /-- Outside `supp`, the substitution is the identity `var x`. -/
  outside_id : ∀ x ∉ supp, toFun x = Lam.var x

namespace Subst

instance : CoeFun Subst (fun _ => Atom → Lam) := ⟨Subst.toFun⟩

@[simp] theorem coe_mk (f : Atom → Lam) (S : Finset Atom) (h) :
    (⟨f, S, h⟩ : Subst) = f := rfl

/-- Codomain support: the atoms mentioned by the substitution's
non-identity image. `supp ∪ ⋃ x ∈ supp, fv (σ x)` is a finite superset
of every atom that could clash with a bound name during `subst`. -/
def codSupp (σ : Subst) : Finset Atom :=
  σ.supp ∪ σ.supp.biUnion (fun x => Lam.fv (σ.toFun x))

theorem supp_subset_codSupp (σ : Subst) : σ.supp ⊆ σ.codSupp :=
  fun _ hx => Finset.mem_union.mpr (Or.inl hx)

/-- Identity substitution: sends every atom to itself. -/
def id : Subst where
  toFun := Lam.var
  supp := ∅
  outside_id := fun _ _ => rfl

@[simp] theorem id_apply (x : Atom) : Subst.id x = Lam.var x := rfl

/-- Extend a substitution: `σ.update a u` sends `a` to `u` and every
other atom via `σ`. Enlarges the support by `a`. -/
def update (σ : Subst) (a : Atom) (u : Lam) : Subst where
  toFun := Function.update σ.toFun a u
  supp := insert a σ.supp
  outside_id := by
    intro x hx
    have hxa : x ≠ a := fun h => hx (h ▸ Finset.mem_insert_self a σ.supp)
    have hxsupp : x ∉ σ.supp :=
      fun h => hx (Finset.mem_insert_of_mem h)
    change Function.update σ.toFun a u x = Lam.var x
    rw [Function.update_of_ne hxa]
    exact σ.outside_id x hxsupp

@[simp] theorem update_apply_same (σ : Subst) (a : Atom) (u : Lam) :
    (σ.update a u).toFun a = u := by
  change Function.update σ.toFun a u a = u
  exact Function.update_self a u σ.toFun

@[simp] theorem update_apply_ne (σ : Subst) (a : Atom) (u : Lam)
    {x : Atom} (h : x ≠ a) :
    (σ.update a u).toFun x = σ.toFun x := by
  change Function.update σ.toFun a u x = σ.toFun x
  exact Function.update_of_ne h u σ.toFun

/-! ### Fresh atom for a substitution

The pivotal fact for the `lam` case of `RawLam.subst` (and later, the
FSP-based SRA axioms): given any substitution `σ` and any finite
set `A`, there exists an atom outside `A` and outside `σ.codSupp`.
`freshAtom` computes such an atom, `freshAtom_notMem_*` witness. -/

/-- A fresh atom for a substitution against an auxiliary finite set.
Uses `_root_.id` because `id` in this namespace resolves to
`Subst.id`. -/
def freshAtom (σ : Subst) (A : Finset Atom) : Atom :=
  (A ∪ σ.codSupp).sup _root_.id + 1

theorem freshAtom_notMem (σ : Subst) (A : Finset Atom) :
    σ.freshAtom A ∉ A ∪ σ.codSupp := by
  intro hmem
  have h : (A ∪ σ.codSupp).sup _root_.id + 1 ≤ (A ∪ σ.codSupp).sup _root_.id :=
    Finset.le_sup (f := _root_.id) hmem
  exact Nat.not_succ_le_self _ h

theorem freshAtom_notMem_left (σ : Subst) (A : Finset Atom) :
    σ.freshAtom A ∉ A :=
  fun h => σ.freshAtom_notMem A (Finset.mem_union.mpr (Or.inl h))

theorem freshAtom_notMem_codSupp (σ : Subst) (A : Finset Atom) :
    σ.freshAtom A ∉ σ.codSupp :=
  fun h => σ.freshAtom_notMem A (Finset.mem_union.mpr (Or.inr h))

/-! ### `Perm` action on `Subst`

`(π • σ) x := π • (σ (π⁻¹ • x))` — the standard function-space action
specialised to `Atom → Lam`. Support conjugates: `(π • σ).supp =
π • σ.supp`. Needed for the equivariance of `Lam.subst` and hence of
the SRA `subst` operation. -/

/-- Underlying smul function, so `MulAction` laws can reference it
without self-recursion in the instance body. -/
def smulFn (π : Perm) (σ : Subst) : Subst where
  toFun := fun x => π • (σ (π⁻¹ • x))
  supp := σ.supp.image (fun a => π • a)
  outside_id := by
    intro x hx
    have h : π⁻¹ • x ∉ σ.supp := by
      intro hin
      apply hx
      rw [Finset.mem_image]
      refine ⟨π⁻¹ • x, hin, ?_⟩
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [σ.outside_id _ h]
    change π • (Lam.var (π⁻¹ • x)) = Lam.var x
    simp only [Lam.smul_var]
    rw [← mul_smul, mul_inv_cancel, one_smul]

/-- Action of a permutation on a substitution, componentwise-conjugated. -/
instance instMulAction : MulAction Perm Subst where
  smul := smulFn
  one_smul σ := by
    change smulFn 1 σ = σ
    refine Subst.ext ?_ ?_
    · funext x
      change (1 : Perm) • (σ.toFun ((1 : Perm)⁻¹ • x)) = σ.toFun x
      rw [inv_one, one_smul, one_smul]
    · change σ.supp.image (fun a => (1 : Perm) • a) = σ.supp
      have hid : (fun a : Atom => (1 : Perm) • a) = _root_.id := by
        funext a; exact one_smul _ _
      rw [hid, Finset.image_id]
  mul_smul π₁ π₂ σ := by
    change smulFn (π₁ * π₂) σ = smulFn π₁ (smulFn π₂ σ)
    refine Subst.ext ?_ ?_
    · funext x
      change (π₁ * π₂) • (σ.toFun ((π₁ * π₂)⁻¹ • x))
         = π₁ • ((smulFn π₂ σ).toFun (π₁⁻¹ • x))
      change (π₁ * π₂) • (σ.toFun ((π₁ * π₂)⁻¹ • x))
         = π₁ • (π₂ • (σ.toFun (π₂⁻¹ • π₁⁻¹ • x)))
      rw [mul_smul, mul_inv_rev, mul_smul]
    · change σ.supp.image (fun a => (π₁ * π₂) • a)
         = (σ.supp.image (fun a => π₂ • a)).image (fun a => π₁ • a)
      rw [Finset.image_image]
      apply Finset.image_congr
      intros a _
      exact mul_smul π₁ π₂ a

@[simp] theorem smul_apply (π : Perm) (σ : Subst) (x : Atom) :
    (π • σ : Subst).toFun x = π • (σ.toFun (π⁻¹ • x)) := rfl

@[simp] theorem smul_supp (π : Perm) (σ : Subst) :
    (π • σ : Subst).supp = σ.supp.image (fun a => π • a) := rfl

/-! ### Small algebraic identities on `update`

Two updates at the same atom collapse to the second; equivariance of
`update`. Used pervasively in the substitution proofs below. -/

/-- Overwriting an atom's assignment: the second value wins. -/
theorem update_update_same (σ : Subst) (a : Atom) (u v : Lam) :
    (σ.update a u).update a v = σ.update a v := by
  refine Subst.ext ?_ ?_
  · funext x
    by_cases hx : x = a
    · rw [hx]
      rw [update_apply_same, update_apply_same]
    · rw [update_apply_ne _ _ _ hx, update_apply_ne _ _ _ hx,
          update_apply_ne _ _ _ hx]
  · change insert a (insert a σ.supp) = insert a σ.supp
    rw [Finset.insert_idem]

/-- Updates at distinct atoms commute. -/
theorem update_update_comm (σ : Subst) {a b : Atom} (hab : a ≠ b)
    (u v : Lam) :
    (σ.update a u).update b v = (σ.update b v).update a u := by
  refine Subst.ext ?_ ?_
  · funext x
    by_cases hxa : x = a
    · subst hxa
      rw [update_apply_ne _ _ _ hab.symm.symm, update_apply_same,
          update_apply_same]
      -- Wait: (σ.update x u).update b v at x: since x ≠ b (hab), it's (σ.update x u) x = u.
      -- (σ.update b v).update x u at x: it's u.
    · by_cases hxb : x = b
      · subst hxb
        rw [update_apply_same, update_apply_ne _ _ _ hxa,
            update_apply_same]
      · rw [update_apply_ne _ _ _ hxb, update_apply_ne _ _ _ hxa,
            update_apply_ne _ _ _ hxa, update_apply_ne _ _ _ hxb]
  · change insert b (insert a σ.supp) = insert a (insert b σ.supp)
    exact Finset.insert_comm b a σ.supp

/-- Equivariance of `update`: the action distributes over updating. -/
theorem smul_update (π : Perm) (σ : Subst) (a : Atom) (u : Lam) :
    π • (σ.update a u) = (π • σ).update (π • a) (π • u) := by
  refine Subst.ext ?_ ?_
  · funext x
    show (π • σ.update a u).toFun x
      = ((π • σ).update (π • a) (π • u)).toFun x
    rw [smul_apply]
    by_cases hx : x = π • a
    · subst hx
      have : π⁻¹ • π • a = a := by
        rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [this, update_apply_same, update_apply_same]
    · have hxne : π⁻¹ • x ≠ a := by
        intro heq
        apply hx
        have := congrArg (fun y => π • y) heq
        simp only [← mul_smul, mul_inv_cancel, one_smul] at this
        exact this
      rw [update_apply_ne _ _ _ hxne, update_apply_ne _ _ _ hx]
      change π • σ.toFun (π⁻¹ • x) = (π • σ).toFun x
      rw [smul_apply]
  · change (σ.update a u).supp.image (fun b => π • b)
      = insert (π • a) ((π • σ) : Subst).supp
    change (insert a σ.supp).image (fun b => π • b)
      = insert (π • a) (σ.supp.image (fun b => π • b))
    rw [Finset.image_insert]

/-! ### Codomain support: equivariance and freshness -/

/-- If `c` is outside the codomain support, it's outside the plain
support (since `supp ⊆ codSupp`). -/
theorem notMem_supp_of_notMem_codSupp {σ : Subst} {c : Atom}
    (h : c ∉ σ.codSupp) : c ∉ σ.supp :=
  fun hc => h (σ.supp_subset_codSupp hc)

/-- Outside `supp`, `σ.toFun` is the identity — restated as a plain
lemma for convenience. -/
theorem toFun_of_notMem_supp {σ : Subst} {c : Atom}
    (h : c ∉ σ.supp) : σ.toFun c = Lam.var c :=
  σ.outside_id c h

/-- Outside `codSupp`, `σ.toFun` is the identity. -/
theorem toFun_of_notMem_codSupp {σ : Subst} {c : Atom}
    (h : c ∉ σ.codSupp) : σ.toFun c = Lam.var c :=
  toFun_of_notMem_supp (notMem_supp_of_notMem_codSupp h)

/-- Equivariance of `codSupp`: the action of `π` transports the
codomain support pointwise. -/
theorem codSupp_smul (π : Perm) (σ : Subst) :
    (π • σ).codSupp = σ.codSupp.image (fun a => π • a) := by
  change (π • σ).supp ∪ (π • σ).supp.biUnion
        (fun x => Lam.fv ((π • σ).toFun x))
     = (σ.supp ∪ σ.supp.biUnion (fun x => Lam.fv (σ.toFun x))).image
        (fun a => π • a)
  have hsupp : (π • σ).supp = σ.supp.image (fun a => π • a) := rfl
  rw [hsupp, Finset.image_union]
  congr 1
  rw [Finset.biUnion_image, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro x _
  change Lam.fv (π • σ.toFun (π⁻¹ • π • x))
     = (Lam.fv (σ.toFun x)).image (fun a => π • a)
  have hx : π⁻¹ • π • x = x := by
    rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [hx]
  exact Lam.fv_smul π (σ.toFun x)

/-- `σ` is supported by its codomain support: any permutation fixing
`σ.codSupp` pointwise leaves `σ` unchanged. -/
theorem supports_codSupp (σ : Subst) : Supports σ.codSupp σ := by
  intro π hπ
  refine Subst.ext ?_ ?_
  · funext x
    change π • σ.toFun (π⁻¹ • x) = σ.toFun x
    by_cases hxsupp : x ∈ σ.supp
    · -- x ∈ supp ⊆ codSupp so π fixes x, i.e. π⁻¹ • x = x.
      have hxfix : π • x = x := hπ x (σ.supp_subset_codSupp hxsupp)
      have hxinv : π⁻¹ • x = x := by
        have := congrArg (fun y => π⁻¹ • y) hxfix
        simp only [← mul_smul, inv_mul_cancel, one_smul] at this
        exact this.symm
      rw [hxinv]
      -- Now show π • σ x = σ x. Every atom in fv (σ x) is in codSupp
      -- (via biUnion), so π fixes it. Use supports_fv.
      have hfv : ∀ a ∈ Lam.fv (σ.toFun x), π • a = a := by
        intro a ha
        apply hπ
        refine Finset.mem_union.mpr (Or.inr ?_)
        exact Finset.mem_biUnion.mpr ⟨x, hxsupp, ha⟩
      exact Lam.supports_fv (σ.toFun x) π hfv
    · -- x ∉ supp: σ x = var x, and we need π • σ (π⁻¹ x) = var x.
      -- Need: π⁻¹ x = π⁻¹ x, and π⁻¹ x ∉ supp too (since π fixes supp).
      have hxinv_notin : π⁻¹ • x ∉ σ.supp := by
        intro hin
        apply hxsupp
        have hxfix : π • (π⁻¹ • x) = π⁻¹ • x :=
          hπ (π⁻¹ • x) (σ.supp_subset_codSupp hin)
        rw [← mul_smul, mul_inv_cancel, one_smul] at hxfix
        exact hxfix ▸ hin
      rw [toFun_of_notMem_supp hxinv_notin, toFun_of_notMem_supp hxsupp]
      change π • Lam.var (π⁻¹ • x) = Lam.var x
      rw [Lam.smul_var]
      congr 1
      rw [← mul_smul, mul_inv_cancel, one_smul]
  · change σ.supp.image (fun a => π • a) = σ.supp
    apply Finset.ext
    intro a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbfix : π • b = b := hπ b (σ.supp_subset_codSupp hb)
      rw [hbfix]
      exact hb
    · intro ha
      refine ⟨a, ha, ?_⟩
      exact hπ a (σ.supp_subset_codSupp ha)

/-- Specialisation of `supports_codSupp` to a swap of two fresh
atoms. Both atoms being outside the codomain support means `swap` acts
identically on `σ`. -/
theorem swap_smul_eq_self_of_notMem_codSupp (σ : Subst)
    {c d : Atom} (hc : c ∉ σ.codSupp) (hd : d ∉ σ.codSupp) :
    swap c d • σ = σ := by
  apply supports_codSupp
  intro a ha
  have hac : a ≠ c := fun h => hc (h ▸ ha)
  have had : a ≠ d := fun h => hd (h ▸ ha)
  change Equiv.swap c d a = a
  exact Equiv.swap_apply_of_ne_of_ne hac had

end Subst

/-! ### Capture-avoiding substitution on raw terms

`RawLam.subst σ t : Lam` substitutes `σ` into a raw term, producing an
α-equivalence class. The `lam` case picks a fresh binder atom (via
`σ.freshAtom`) outside `σ.codSupp` and the free variables of the
outer term, so no capture can occur. The recursion is structural on
the target `RawLam`. -/

namespace RawLam

/-- Capture-avoiding substitution.

For the `lam` case, we pick a fresh binder atom outside every atom
already in play — the codomain support `σ.codSupp` and every atom
mentioned in the raw body (`allAtoms (lam a t)`, i.e. `a` itself plus
the bound and free atoms of `t`). Using `allAtoms` rather than `fv`
here is a mild strengthening that lets us later prove the swap-based
substitution lemmas without having to α-rename the body first: the
chosen atom cannot collide with any bound name inside `t`. -/
def subst (σ : Subst) : RawLam → Lam
  | var x    => σ x
  | app t s  => Lam.app (subst σ t) (subst σ s)
  | lam a t  =>
      let a' := σ.freshAtom (allAtoms (lam a t))
      Lam.lam a' (subst (σ.update a (Lam.var a')) t)

@[simp] theorem subst_var (σ : Subst) (x : Atom) :
    subst σ (var x) = σ x := rfl

@[simp] theorem subst_app (σ : Subst) (t s : RawLam) :
    subst σ (app t s) = Lam.app (subst σ t) (subst σ s) := rfl

theorem subst_lam (σ : Subst) (a : Atom) (t : RawLam) :
    subst σ (lam a t)
      = Lam.lam (σ.freshAtom (allAtoms (lam a t)))
          (subst (σ.update a (Lam.var (σ.freshAtom (allAtoms (lam a t))))) t) := rfl

/-! ### Equivariance of `allAtoms`

Analogous to `fv_smul` — permutations transport the set of atoms
pointwise. Used to transport freshness conditions across the action. -/

/-- `allAtoms` commutes with the action of `π`. -/
theorem allAtoms_smul (π : Perm) (t : RawLam) :
    allAtoms (π • t) = (allAtoms t).image (fun a => π • a) := by
  induction t with
  | var a =>
      change ({π • a} : Finset Atom) = ({a} : Finset Atom).image (fun x => π • x)
      rw [Finset.image_singleton]
  | app t s iht ihs =>
      change allAtoms (π • t) ∪ allAtoms (π • s)
        = (allAtoms t ∪ allAtoms s).image (fun a => π • a)
      rw [iht, ihs, Finset.image_union]
  | lam a t ih =>
      change insert (π • a) (allAtoms (π • t))
        = (insert a (allAtoms t)).image (fun x => π • x)
      rw [ih, Finset.image_insert]

/-! ### Free-variable containment for `subst`

The set of free variables of `subst σ t` is contained in the atoms
"reachable" from `t` via `σ`: any atom that is neither in `σ.codSupp`
nor in `allAtoms t` cannot appear free in the result. This is the key
freshness lemma needed to rewrite results with `Lam.lam_alpha` in the
proofs below. -/

/-- Every free atom of `subst σ t` lies in `σ.codSupp ∪ allAtoms t`. -/
theorem fv_subst_subset (σ : Subst) (t : RawLam) :
    Lam.fv (subst σ t) ⊆ σ.codSupp ∪ allAtoms t := by
  induction t generalizing σ with
  | var x =>
      -- subst σ (var x) = σ x; fv (σ x) ⊆ σ.codSupp ∪ {x}.
      intro a ha
      change a ∈ Lam.fv (σ.toFun x) at ha
      by_cases hx : x ∈ σ.supp
      · -- fv (σ x) ⊆ codSupp.
        refine Finset.mem_union.mpr (Or.inl ?_)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨x, hx, ha⟩))
      · -- σ x = var x, so fv (σ x) = {x}.
        rw [σ.outside_id x hx] at ha
        change a ∈ ({x} : Finset Atom) at ha
        rw [Finset.mem_singleton] at ha
        subst ha
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  | app t s iht ihs =>
      intro a ha
      change a ∈ Lam.fv (Lam.app (subst σ t) (subst σ s)) at ha
      rw [Lam.fv_app] at ha
      rcases Finset.mem_union.mp ha with hat | has
      · have := iht σ hat
        rcases Finset.mem_union.mp this with hcs | hat'
        · exact Finset.mem_union.mpr (Or.inl hcs)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hat')))
      · have := ihs σ has
        rcases Finset.mem_union.mp this with hcs | has'
        · exact Finset.mem_union.mpr (Or.inl hcs)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr has')))
  | lam d t' ih =>
      intro a ha
      set a' := σ.freshAtom (allAtoms (lam d t')) with ha'_def
      change a ∈ Lam.fv (Lam.lam a' (subst (σ.update d (Lam.var a')) t')) at ha
      rw [Lam.fv_lam] at ha
      have haa' : a ≠ a' := fun h =>
        (Finset.mem_sdiff.mp ha).2 (Finset.mem_singleton.mpr h)
      have hin : a ∈ Lam.fv (subst (σ.update d (Lam.var a')) t') :=
        (Finset.mem_sdiff.mp ha).1
      have := ih (σ.update d (Lam.var a')) hin
      -- Analyze: a ∈ (σ.update d (Lam.var a')).codSupp ∪ allAtoms t'.
      rcases Finset.mem_union.mp this with hcs | hat'
      · -- a is in the codSupp of the updated substitution.
        -- (σ.update d (Lam.var a')).codSupp:
        --   supp = insert d σ.supp
        --   biUnion → for x ∈ insert d σ.supp:
        --     if x = d: fv (Lam.var a') = {a'}
        --     else: fv (σ x) (subset of σ.codSupp)
        rcases Finset.mem_union.mp hcs with hsupp | hbi
        · -- a ∈ insert d σ.supp
          rcases Finset.mem_insert.mp hsupp with had | hasupp
          · -- a = d
            refine Finset.mem_union.mpr (Or.inr ?_)
            change a ∈ insert d (allAtoms t')
            exact Finset.mem_insert.mpr (Or.inl had)
          · -- a ∈ σ.supp
            refine Finset.mem_union.mpr (Or.inl ?_)
            exact σ.supp_subset_codSupp hasupp
        · -- a ∈ biUnion
          rw [Finset.mem_biUnion] at hbi
          obtain ⟨x, hxsupp, hxfv⟩ := hbi
          rcases Finset.mem_insert.mp hxsupp with hxd | hxsupp'
          · -- x = d
            subst hxd
            change a ∈ Lam.fv (Function.update σ.toFun x (Lam.var a') x) at hxfv
            rw [Function.update_self] at hxfv
            change a ∈ ({a'} : Finset Atom) at hxfv
            rw [Finset.mem_singleton] at hxfv
            exact absurd hxfv haa'
          · -- x ∈ σ.supp, x ≠ d (in general — but Function.update at d might interfere)
            change a ∈ Lam.fv (Function.update σ.toFun d (Lam.var a') x) at hxfv
            by_cases hxd : x = d
            · subst hxd
              rw [Function.update_self] at hxfv
              change a ∈ ({a'} : Finset Atom) at hxfv
              rw [Finset.mem_singleton] at hxfv
              exact absurd hxfv haa'
            · rw [Function.update_of_ne hxd] at hxfv
              refine Finset.mem_union.mpr (Or.inl ?_)
              refine Finset.mem_union.mpr (Or.inr ?_)
              exact Finset.mem_biUnion.mpr ⟨x, hxsupp', hxfv⟩
      · -- a ∈ allAtoms t' ⊆ allAtoms (lam d t')
        refine Finset.mem_union.mpr (Or.inr ?_)
        change a ∈ insert d (allAtoms t')
        exact Finset.mem_insert_of_mem hat'

/-- Contrapositive form: if `c` is outside both `σ.codSupp` and
`allAtoms t`, it does not appear free in the substitution's result. -/
theorem fv_subst_notMem {σ : Subst} {t : RawLam} {c : Atom}
    (hcs : c ∉ σ.codSupp) (ht : c ∉ allAtoms t) :
    c ∉ Lam.fv (subst σ t) := by
  intro hin
  rcases Finset.mem_union.mp (fv_subst_subset σ t hin) with h | h
  · exact hcs h
  · exact ht h

/-- Tighter fv bound: every free variable of the substitution result
is a free variable of `σ` at some free variable of `t`. This is the
"σ can only inject atoms it actually mentions in images of `fv t`"
statement, refining `fv_subst_subset`. -/
theorem fv_subst_subset_tight (σ : Subst) (t : RawLam) :
    Lam.fv (subst σ t)
      ⊆ (fv t).biUnion (fun x => Lam.fv (σ.toFun x)) := by
  induction t generalizing σ with
  | var x =>
      intro a ha
      change a ∈ Lam.fv (σ.toFun x) at ha
      refine Finset.mem_biUnion.mpr ⟨x, ?_, ha⟩
      exact Finset.mem_singleton.mpr rfl
  | app t s iht ihs =>
      intro a ha
      change a ∈ Lam.fv (Lam.app (subst σ t) (subst σ s)) at ha
      rw [Lam.fv_app] at ha
      rcases Finset.mem_union.mp ha with hat | has
      · have := iht σ hat
        rw [Finset.mem_biUnion] at this
        obtain ⟨x, hx, hxfv⟩ := this
        refine Finset.mem_biUnion.mpr ⟨x, ?_, hxfv⟩
        change x ∈ fv t ∪ fv s
        exact Finset.mem_union.mpr (Or.inl hx)
      · have := ihs σ has
        rw [Finset.mem_biUnion] at this
        obtain ⟨x, hx, hxfv⟩ := this
        refine Finset.mem_biUnion.mpr ⟨x, ?_, hxfv⟩
        change x ∈ fv t ∪ fv s
        exact Finset.mem_union.mpr (Or.inr hx)
  | lam d t' ih =>
      intro a ha
      set a' := σ.freshAtom (allAtoms (lam d t')) with ha'_def
      change a ∈ Lam.fv (Lam.lam a' (subst (σ.update d (Lam.var a')) t')) at ha
      rw [Lam.fv_lam] at ha
      have haa' : a ≠ a' := fun h =>
        (Finset.mem_sdiff.mp ha).2 (Finset.mem_singleton.mpr h)
      have hin : a ∈ Lam.fv (subst (σ.update d (Lam.var a')) t') :=
        (Finset.mem_sdiff.mp ha).1
      have hbi := ih (σ.update d (Lam.var a')) hin
      rw [Finset.mem_biUnion] at hbi
      obtain ⟨x, hxfv, hxin⟩ := hbi
      change a ∈ Lam.fv (Function.update σ.toFun d (Lam.var a') x) at hxin
      -- Case x = d.
      by_cases hxd : x = d
      · subst hxd
        rw [Function.update_self] at hxin
        change a ∈ ({a'} : Finset Atom) at hxin
        rw [Finset.mem_singleton] at hxin
        exact absurd hxin haa'
      · rw [Function.update_of_ne hxd] at hxin
        refine Finset.mem_biUnion.mpr ⟨x, ?_, hxin⟩
        change x ∈ fv t' \ {d}
        exact Finset.mem_sdiff.mpr ⟨hxfv,
          fun h => hxd (Finset.mem_singleton.mp h)⟩

/-! ### Raw-level equivariance of `subst`

The key structural fact underlying every subsequent property of
substitution: `π • subst σ t = subst (π • σ) (π • t)`. Because the
`lam` case introduces a fresh binder atom deterministically from `σ`
and `t`, the LHS's binder atom `π • σ.freshAtom(...)` differs from the
RHS's `(π • σ).freshAtom(...)`. Both are however fresh for the *same*
data (transported by π), and the resulting `Lam` values coincide via
α-equivalence — bridged by `Lam.lam_alpha` and an internal renaming
lemma proved in the same induction step. -/

/-- Bridging lemma used inside the `lam` case of `subst_perm`.

Given two atoms `e₁, e₂` both fresh for the codomain support of `σ`
and for every atom of `lam d t'`, the two "canonical" substitution
unfoldings with binder atoms `e₁` and `e₂` yield equal `Lam` values.
Established here as a helper hypothesis passed through the induction:
we need the outer equivariance IH to prove it, and we use it in the
outer step. -/
private theorem subst_lam_freshBinder_of_perm
    (σ : Subst) (d : Atom) (t' : RawLam)
    (ih : ∀ (σ' : Subst) (π' : Perm),
      π' • subst σ' t' = subst (π' • σ') (π' • t'))
    {e₁ e₂ : Atom}
    (he₁ : e₁ ∉ σ.codSupp ∪ allAtoms (lam d t'))
    (he₂ : e₂ ∉ σ.codSupp ∪ allAtoms (lam d t')) :
    Lam.lam e₁ (subst (σ.update d (Lam.var e₁)) t')
      = Lam.lam e₂ (subst (σ.update d (Lam.var e₂)) t') := by
  by_cases heq : e₁ = e₂
  · rw [heq]
  -- Decompose freshness data.
  have he₁cs : e₁ ∉ σ.codSupp := fun h =>
    he₁ (Finset.mem_union.mpr (Or.inl h))
  have he₁a : e₁ ∉ allAtoms (lam d t') := fun h =>
    he₁ (Finset.mem_union.mpr (Or.inr h))
  have he₁d : e₁ ≠ d := fun h => he₁a (h ▸ Finset.mem_insert_self _ _)
  have he₁t : e₁ ∉ allAtoms t' := fun h =>
    he₁a (Finset.mem_insert_of_mem h)
  have he₂cs : e₂ ∉ σ.codSupp := fun h =>
    he₂ (Finset.mem_union.mpr (Or.inl h))
  have he₂a : e₂ ∉ allAtoms (lam d t') := fun h =>
    he₂ (Finset.mem_union.mpr (Or.inr h))
  have he₂d : e₂ ≠ d := fun h => he₂a (h ▸ Finset.mem_insert_self _ _)
  have he₂t : e₂ ∉ allAtoms t' := fun h =>
    he₂a (Finset.mem_insert_of_mem h)
  -- Setup: X_e := subst (σ.update d (Lam.var e)) t'.
  set X₁ : Lam := subst (σ.update d (Lam.var e₁)) t' with hX₁_def
  set X₂ : Lam := subst (σ.update d (Lam.var e₂)) t' with hX₂_def
  -- First, show e₂ ∉ Lam.fv X₁, so Lam.lam_alpha applies.
  have hcodSupp₁ : e₂ ∉ (σ.update d (Lam.var e₁)).codSupp := by
    intro hin
    rcases Finset.mem_union.mp hin with hsupp | hbi
    · -- e₂ ∈ insert d σ.supp
      rcases Finset.mem_insert.mp hsupp with hd' | hσ
      · exact he₂d hd'
      · exact he₂cs (σ.supp_subset_codSupp hσ)
    · -- e₂ ∈ biUnion
      rw [Finset.mem_biUnion] at hbi
      obtain ⟨x, hx, hxfv⟩ := hbi
      change e₂ ∈ Lam.fv (Function.update σ.toFun d (Lam.var e₁) x) at hxfv
      by_cases hxd : x = d
      · subst hxd
        rw [Function.update_self] at hxfv
        change e₂ ∈ ({e₁} : Finset Atom) at hxfv
        rw [Finset.mem_singleton] at hxfv
        exact heq hxfv.symm
      · rw [Function.update_of_ne hxd] at hxfv
        rcases Finset.mem_insert.mp hx with hxd' | hxsupp
        · exact hxd hxd'
        · exact he₂cs (Finset.mem_union.mpr
            (Or.inr (Finset.mem_biUnion.mpr ⟨x, hxsupp, hxfv⟩)))
  have he₂fv : e₂ ∉ Lam.fv X₁ :=
    fv_subst_notMem hcodSupp₁ he₂t
  -- Apply Lam.lam_alpha to rename e₁ to e₂ in the outer binder.
  rw [Lam.lam_alpha e₁ e₂ X₁ (Or.inl he₂fv)]
  -- Now goal: Lam.lam e₂ (swap e₁ e₂ • X₁) = Lam.lam e₂ X₂.
  -- Reduce swap e₁ e₂ • X₁ using the equivariance IH.
  congr 1
  show swap e₁ e₂ • X₁ = X₂
  rw [hX₁_def]
  rw [ih (σ.update d (Lam.var e₁)) (swap e₁ e₂)]
  -- Now: subst (swap e₁ e₂ • (σ.update d (Lam.var e₁))) (swap e₁ e₂ • t')
  --    = X₂ = subst (σ.update d (Lam.var e₂)) t'.
  -- Simplify swap e₁ e₂ • t' = t' via supports_allAtoms.
  have ht' : (swap e₁ e₂ : Perm) • t' = t' := by
    apply supports_allAtoms
    intro a ha
    have hae₁ : a ≠ e₁ := fun h => he₁t (h ▸ ha)
    have hae₂ : a ≠ e₂ := fun h => he₂t (h ▸ ha)
    change Equiv.swap e₁ e₂ a = a
    exact Equiv.swap_apply_of_ne_of_ne hae₁ hae₂
  rw [ht']
  rw [hX₂_def]
  -- Now: subst (swap e₁ e₂ • (σ.update d (Lam.var e₁))) t'
  --    = subst (σ.update d (Lam.var e₂)) t'.
  -- Reduce swap e₁ e₂ • (σ.update d (Lam.var e₁)) via smul_update.
  rw [Subst.smul_update]
  -- Now: subst ((swap e₁ e₂ • σ).update (swap e₁ e₂ • d) (swap e₁ e₂ • Lam.var e₁)) t'
  --    = subst (σ.update d (Lam.var e₂)) t'.
  congr 1
  -- swap e₁ e₂ • σ = σ:
  have hσ : (swap e₁ e₂ : Perm) • σ = σ :=
    Subst.swap_smul_eq_self_of_notMem_codSupp σ he₁cs he₂cs
  rw [hσ]
  -- swap e₁ e₂ • d = d:
  have hdswap : (swap e₁ e₂ : Perm) • d = d := by
    change Equiv.swap e₁ e₂ d = d
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm he₁d) (Ne.symm he₂d)
  rw [hdswap]
  -- swap e₁ e₂ • Lam.var e₁ = Lam.var e₂:
  change σ.update d (swap e₁ e₂ • Lam.var e₁) = σ.update d (Lam.var e₂)
  congr 1
  rw [Lam.smul_var]
  congr 1
  change Equiv.swap e₁ e₂ e₁ = e₂
  exact Equiv.swap_apply_left e₁ e₂

/-- Raw-level equivariance of `subst`: applying `π` to the result of
substituting `σ` into `t` is the same as substituting `π • σ` into
`π • t`. Proved by structural induction on `t`, using
`subst_lam_freshBinder_of_perm` to reconcile the mismatched fresh
binder atoms in the `lam` case. -/
theorem subst_perm (σ : Subst) (π : Perm) (t : RawLam) :
    π • subst σ t = subst (π • σ) (π • t) := by
  induction t generalizing σ π with
  | var x =>
      change π • σ.toFun x = (π • σ).toFun (π • x)
      rw [Subst.smul_apply]
      congr 1
      rw [← mul_smul, inv_mul_cancel, one_smul]
  | app t s iht ihs =>
      change π • (Lam.app (subst σ t) (subst σ s))
        = Lam.app (subst (π • σ) (π • t)) (subst (π • σ) (π • s))
      rw [Lam.smul_app, iht, ihs]
  | lam d t' ih =>
      -- LHS = π • subst σ (lam d t'); unfold and apply IH to `t'`.
      set a := σ.freshAtom (allAtoms (lam d t')) with ha_def
      change π • (Lam.lam a (subst (σ.update d (Lam.var a)) t'))
        = subst (π • σ) (lam (π • d) (π • t'))
      rw [Lam.smul_lam, ih (σ.update d (Lam.var a)) π,
          Subst.smul_update, Lam.smul_var]
      -- Now LHS = Lam.lam (π • a) (subst ((π•σ).update (π•d) (Lam.var (π•a))) (π • t')).
      -- Unfold RHS to its `Lam.lam _ (subst _ _)` form.
      change Lam.lam (π • a)
          (subst ((π • σ).update (π • d) (Lam.var (π • a))) (π • t'))
        = Lam.lam ((π • σ).freshAtom (allAtoms (lam (π • d) (π • t'))))
          (subst ((π • σ).update (π • d)
            (Lam.var ((π • σ).freshAtom (allAtoms
              (lam (π • d) (π • t')))))) (π • t'))
      -- Freshness data for π • a.
      have ha_notMem : a ∉ allAtoms (lam d t') ∪ σ.codSupp :=
        σ.freshAtom_notMem (allAtoms (lam d t'))
      have ha_a : a ∉ allAtoms (lam d t') := fun h =>
        ha_notMem (Finset.mem_union.mpr (Or.inl h))
      have ha_cs : a ∉ σ.codSupp := fun h =>
        ha_notMem (Finset.mem_union.mpr (Or.inr h))
      -- Show π • a ∉ (π • σ).codSupp ∪ allAtoms (lam (π • d) (π • t')).
      have hπa : π • a ∉ (π • σ).codSupp
          ∪ allAtoms (lam (π • d) (π • t')) := by
        intro hin
        rcases Finset.mem_union.mp hin with h₁ | h₂
        · -- π • a ∈ π • σ.codSupp → a ∈ σ.codSupp, contradicting ha_cs.
          rw [Subst.codSupp_smul, Finset.mem_image] at h₁
          obtain ⟨y, hy, hyeq⟩ := h₁
          have hya : y = a := by
            have hcancel : π⁻¹ • π • y = π⁻¹ • π • a := by rw [hyeq]
            rw [← mul_smul, inv_mul_cancel, one_smul,
                ← mul_smul, inv_mul_cancel, one_smul] at hcancel
            exact hcancel
          subst hya
          exact ha_cs hy
        · -- π • a ∈ allAtoms (lam (π•d) (π•t')) = π • allAtoms (lam d t'),
          -- so a ∈ allAtoms (lam d t'), contradicting ha_a.
          have : allAtoms (lam (π • d) (π • t'))
              = (allAtoms (lam d t')).image (fun x => π • x) := by
            change insert (π • d) (allAtoms (π • t'))
                = (insert d (allAtoms t')).image (fun x => π • x)
            rw [allAtoms_smul, Finset.image_insert]
          rw [this, Finset.mem_image] at h₂
          obtain ⟨y, hy, hyeq⟩ := h₂
          have hya : y = a := by
            have hcancel : π⁻¹ • π • y = π⁻¹ • π • a := by rw [hyeq]
            rw [← mul_smul, inv_mul_cancel, one_smul,
                ← mul_smul, inv_mul_cancel, one_smul] at hcancel
            exact hcancel
          subst hya
          exact ha_a hy
      -- Freshness of b.
      set b := (π • σ).freshAtom (allAtoms (lam (π • d) (π • t'))) with hb_def
      have hb : b ∉ (π • σ).codSupp
          ∪ allAtoms (lam (π • d) (π • t')) := by
        have := (π • σ).freshAtom_notMem (allAtoms (lam (π • d) (π • t')))
        intro h
        apply this
        rcases Finset.mem_union.mp h with h | h
        · exact Finset.mem_union.mpr (Or.inr h)
        · exact Finset.mem_union.mpr (Or.inl h)
      -- Apply the bridging lemma to identify Lam.lam (π•a) X = Lam.lam b Y.
      -- Rewrite hπa and hb to the shape expected by the bridging lemma.
      have hπa' : π • a ∉ (π • σ).codSupp ∪ allAtoms (lam (π • d) (π • t')) := hπa
      have hb' : b ∉ (π • σ).codSupp ∪ allAtoms (lam (π • d) (π • t')) := hb
      -- Bridging lemma requires IH-form on `π • t'`. Derive it from the outer
      -- IH by two applications: transport σ' back through π, then out.
      have ih_pit' : ∀ (σ' : Subst) (π' : Perm),
          π' • subst σ' (π • t') = subst (π' • σ') (π' • π • t') := by
        intro σ' π'
        -- Step 1: subst σ' (π • t') = π • subst (π⁻¹ • σ') t'.
        have h1 : subst σ' (π • t') = π • subst (π⁻¹ • σ') t' := by
          rw [ih (π⁻¹ • σ') π]
          congr 1
          rw [← mul_smul, mul_inv_cancel, one_smul]
        rw [h1]
        -- Step 2: π' • π • subst (π⁻¹ • σ') t' = subst (π' • σ') (π' • π • t').
        rw [← mul_smul, ih (π⁻¹ • σ') (π' * π), ← mul_smul, mul_assoc,
            mul_inv_cancel, mul_one, mul_smul]
      exact subst_lam_freshBinder_of_perm (π • σ) (π • d) (π • t')
        ih_pit' hπa' hb'

/-! ### Swap-substitution commutation

If `c` is fresh (outside the codomain support of `σ` and outside every
atom of `t`), then swapping `a` with `c` inside `t` and then
substituting by `σ` is the same as substituting by `σ` extended with
`a ↦ Lam.var c`. Proved by structural induction; the `lam` case uses
`subst_lam_freshBinder_of_perm` (via `subst_perm`) to bridge fresh
binder atoms and `Subst.update_update_comm` (or `update_update_same`)
to normalise the double-update. -/

/-- Helper for the `lam` case of `subst_swap`: expressing
`subst σ (lam d t)` via any sufficiently fresh binder atom. -/
theorem subst_lam_freshBinder
    (σ : Subst) (d : Atom) (t : RawLam) {e : Atom}
    (he : e ∉ σ.codSupp ∪ allAtoms (lam d t)) :
    subst σ (lam d t)
      = Lam.lam e (subst (σ.update d (Lam.var e)) t) := by
  set a := σ.freshAtom (allAtoms (lam d t)) with ha_def
  change Lam.lam a (subst (σ.update d (Lam.var a)) t)
    = Lam.lam e (subst (σ.update d (Lam.var e)) t)
  have ha_notMem : a ∉ allAtoms (lam d t) ∪ σ.codSupp :=
    σ.freshAtom_notMem _
  have ha : a ∉ σ.codSupp ∪ allAtoms (lam d t) := fun h =>
    ha_notMem (by
      rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union.mpr (Or.inr h)
      · exact Finset.mem_union.mpr (Or.inl h))
  exact subst_lam_freshBinder_of_perm σ d t
    (subst_perm · · t) ha he

/-- Swap-substitution commutation: substituting after a swap with a
fresh atom is the same as substituting via an extended substitution
with the update at `a` mapping to `Lam.var c`.

Proved by structural induction on `t`. The `d = a ∧ d ∈ σ.codSupp`
sub-sub-case of the `lam` branch remains open (documented inline); it
requires either strong-induction on `sizeOf t`, mutual induction with
an α-renaming lemma, or an α-preserving substitution normalisation. -/
theorem subst_swap (σ : Subst) (a c : Atom) (t : RawLam)
    (hc_cs : c ∉ σ.codSupp) (hc_a : c ∉ allAtoms t) :
    subst σ (swap a c • t) = subst (σ.update a (Lam.var c)) t := by
  induction t generalizing σ a c with
  | var x =>
      change c ∉ ({x} : Finset Atom) at hc_a
      rw [Finset.mem_singleton] at hc_a
      have hcx : c ≠ x := hc_a
      change σ.toFun (swap a c • x) = (σ.update a (Lam.var c)).toFun x
      by_cases hxa : x = a
      · subst hxa
        change σ.toFun (Equiv.swap x c x) = (σ.update x (Lam.var c)).toFun x
        rw [Equiv.swap_apply_left, Subst.update_apply_same]
        exact Subst.toFun_of_notMem_codSupp hc_cs
      · have hswap : swap a c • x = x := by
          change Equiv.swap a c x = x
          exact Equiv.swap_apply_of_ne_of_ne hxa (Ne.symm hcx)
        rw [hswap, Subst.update_apply_ne _ _ _ hxa]
  | app t s iht ihs =>
      have hct : c ∉ allAtoms t := fun h =>
        hc_a (Finset.mem_union.mpr (Or.inl h))
      have hcs : c ∉ allAtoms s := fun h =>
        hc_a (Finset.mem_union.mpr (Or.inr h))
      change Lam.app (subst σ (swap a c • t)) (subst σ (swap a c • s))
        = Lam.app (subst (σ.update a (Lam.var c)) t)
                  (subst (σ.update a (Lam.var c)) s)
      rw [iht σ a c hc_cs hct, ihs σ a c hc_cs hcs]
  | lam d t' ih =>
      have hcd : c ≠ d := fun h =>
        hc_a (h ▸ Finset.mem_insert_self _ _)
      have hct' : c ∉ allAtoms t' := fun h =>
        hc_a (Finset.mem_insert_of_mem h)
      by_cases hac : a = c
      · -- Case a = c: LHS = subst σ (lam d t'). RHS = subst (σ.update a (Lam.var a)) (lam d t').
        -- Since a = c ∉ allAtoms (lam d t'), we have a ≠ d and a ∉ allAtoms t'.
        -- Since a = c ∉ σ.codSupp, σ.toFun a = Lam.var a, and both substitutions
        -- have the same pointwise behavior. But their supps differ. Bridge via
        -- freshBinder with a common atom e fresh for both.
        rw [hac] at *
        rw [show (swap c c : Perm) = 1 from Equiv.swap_self c, one_smul]
        have hcd : c ≠ d := fun h =>
          hc_a (h ▸ Finset.mem_insert_self _ _)
        -- Freshness data recomputed for clarity (already have hc_cs, hct').
        obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
          (σ.codSupp ∪ (σ.update c (Lam.var c)).codSupp
            ∪ allAtoms t' ∪ ({c, d} : Finset Atom))
        have hecs : e ∉ σ.codSupp := fun h => he_prop
          (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inl h))))))
        have he_updcs : e ∉ (σ.update c (Lam.var c)).codSupp := fun h =>
          he_prop (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inr h))))))
        have het : e ∉ allAtoms t' := fun h => he_prop
          (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
        have he_cd : e ∉ ({c, d} : Finset Atom) := fun h => he_prop
          (Finset.mem_union.mpr (Or.inr h))
        have hec : e ≠ c := fun h => he_cd
          (h ▸ Finset.mem_insert_self _ _)
        have hed : e ≠ d := fun h => he_cd
          (h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
        -- Rewrite LHS via freshBinder.
        have hL_fresh : e ∉ σ.codSupp ∪ allAtoms (lam d t') := by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact hecs h
          · change e ∈ insert d (allAtoms t') at h
            rcases Finset.mem_insert.mp h with h | h
            · exact hed h
            · exact het h
        rw [subst_lam_freshBinder σ d t' hL_fresh]
        -- Rewrite RHS via freshBinder.
        have hR_fresh : e ∉ (σ.update c (Lam.var c)).codSupp
            ∪ allAtoms (lam d t') := by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact he_updcs h
          · change e ∈ insert d (allAtoms t') at h
            rcases Finset.mem_insert.mp h with h | h
            · exact hed h
            · exact het h
        rw [subst_lam_freshBinder (σ.update c (Lam.var c)) d t' hR_fresh]
        -- Now: Lam.lam e (subst (σ.update d (Lam.var e)) t')
        --    = Lam.lam e (subst ((σ.update c (Lam.var c)).update d (Lam.var e)) t').
        -- The two substitutions differ: LHS has σ.update d ..., RHS has
        -- (σ.update c (Lam.var c)).update d ... = (σ.update d ...).update c (Lam.var c)
        -- by update_update_comm (since c ≠ d, i.e., cd ≠ 0).
        congr 1
        -- Reduce via update_update_comm (rewrite RHS's double update to
        -- put update at d outermost).
        rw [Subst.update_update_comm σ hcd (Lam.var c) (Lam.var e)]
        -- Now goal: subst (σ.update d (Lam.var e)) t'
        --        = subst ((σ.update d (Lam.var e)).update c (Lam.var c)) t'.
        -- The RHS's outer update at c is redundant since c ∉ allAtoms t' and
        -- c doesn't appear in σ.codSupp (so the effective substitution is the
        -- same on t').
        --
        -- Apply IH (subst_swap on t') with σ' := σ.update d (Lam.var e),
        -- a' := c, c' := c. This gives:
        --   subst (σ.update d (Lam.var e)) (swap c c • t')
        --     = subst ((σ.update d (Lam.var e)).update c (Lam.var c)) t'
        -- when c ∉ σ'.codSupp and c ∉ allAtoms t'. swap c c = 1, so LHS
        -- of IH = subst σ' t'. This gives us our body equality.
        have hc_σ' : c ∉ (σ.update d (Lam.var e)).codSupp := by
          intro h
          rcases Finset.mem_union.mp h with hsupp | hbi
          · rcases Finset.mem_insert.mp hsupp with heq | h'
            · exact hcd heq
            · exact hc_cs (σ.supp_subset_codSupp h')
          · rw [Finset.mem_biUnion] at hbi
            obtain ⟨x, hx, hxfv⟩ := hbi
            change c ∈ Lam.fv (Function.update σ.toFun d (Lam.var e) x) at hxfv
            by_cases hxd : x = d
            · rw [hxd, Function.update_self] at hxfv
              change c ∈ ({e} : Finset Atom) at hxfv
              rw [Finset.mem_singleton] at hxfv
              exact hec.symm hxfv
            · rw [Function.update_of_ne hxd] at hxfv
              rcases Finset.mem_insert.mp hx with heq | h'
              · exact hxd heq
              · exact hc_cs (Finset.mem_union.mpr (Or.inr
                  (Finset.mem_biUnion.mpr ⟨x, h', hxfv⟩)))
        have := ih (σ.update d (Lam.var e)) c c hc_σ' hct'
        rw [show (swap c c : Perm) = 1 from Equiv.swap_self c, one_smul] at this
        exact this
      · -- Case a ≠ c. Split on d = a vs d ≠ a.
        change subst σ (lam (swap a c • d) (swap a c • t'))
          = subst (σ.update a (Lam.var c)) (lam d t')
        -- Compute swap a c • d.
        by_cases hda : d = a
        · -- Case d = a: swap a c • d = c.
          subst hda
          have hswap_d : swap d c • d = c := by
            change Equiv.swap d c d = c
            exact Equiv.swap_apply_left d c
          rw [hswap_d]
          -- LHS = subst σ (lam c (swap d c • t')).
          -- RHS = subst (σ.update d (Lam.var c)) (lam d t').
          -- Pick common fresh e.
          obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
            (σ.codSupp ∪ allAtoms t' ∪ allAtoms (swap d c • t')
              ∪ ({d, c} : Finset Atom))
          have hecs : e ∉ σ.codSupp := fun h => he_prop
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl h))))))
          have het : e ∉ allAtoms t' := fun h => he_prop
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inr h))))))
          have heswap : e ∉ allAtoms (swap d c • t') := fun h => he_prop
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
          have he_atoms : e ∉ ({d, c} : Finset Atom) := fun h => he_prop
            (Finset.mem_union.mpr (Or.inr h))
          have hed : e ≠ d := fun h => he_atoms
            (h ▸ Finset.mem_insert_self _ _)
          have hec : e ≠ c := fun h => he_atoms
            (h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
          -- Rewrite LHS via freshBinder.
          have hL_fresh : e ∉ σ.codSupp ∪ allAtoms (lam c (swap d c • t')) := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · exact hecs h
            · change e ∈ insert c (allAtoms (swap d c • t')) at h
              rcases Finset.mem_insert.mp h with h | h
              · exact hec h
              · exact heswap h
          rw [subst_lam_freshBinder σ c (swap d c • t') hL_fresh]
          -- LHS = Lam.lam e (subst (σ.update c (Lam.var e)) (swap d c • t')).
          -- Rewrite RHS via freshBinder.
          have hR_fresh : e ∉ (σ.update d (Lam.var c)).codSupp
              ∪ allAtoms (lam d t') := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · rcases Finset.mem_union.mp h with hsupp | hbi
              · rcases Finset.mem_insert.mp hsupp with heq | h'
                · exact hed heq
                · exact hecs (σ.supp_subset_codSupp h')
              · rw [Finset.mem_biUnion] at hbi
                obtain ⟨x, hx, hxfv⟩ := hbi
                change e ∈ Lam.fv (Function.update σ.toFun d (Lam.var c) x) at hxfv
                by_cases hxd : x = d
                · subst hxd
                  rw [Function.update_self] at hxfv
                  change e ∈ ({c} : Finset Atom) at hxfv
                  rw [Finset.mem_singleton] at hxfv
                  exact hec hxfv
                · rw [Function.update_of_ne hxd] at hxfv
                  rcases Finset.mem_insert.mp hx with heq | h'
                  · exact hxd heq
                  · exact hecs (Finset.mem_union.mpr (Or.inr
                      (Finset.mem_biUnion.mpr ⟨x, h', hxfv⟩)))
            · change e ∈ insert d (allAtoms t') at h
              rcases Finset.mem_insert.mp h with h | h
              · exact hed h
              · exact het h
          rw [subst_lam_freshBinder (σ.update d (Lam.var c)) d t' hR_fresh]
          -- Goal: Lam.lam e (subst (σ.update c (Lam.var e)) (swap d c • t'))
          --     = Lam.lam e (subst ((σ.update d (Lam.var c)).update d (Lam.var e)) t').
          -- RHS's double update at d collapses to σ.update d (Lam.var e).
          rw [Subst.update_update_same]
          congr 1
          -- Goal: subst (σ.update c (Lam.var e)) (swap d c • t')
          --     = subst (σ.update d (Lam.var e)) t'.
          -- Strategy: apply subst_perm with π := swap d c to the LHS, and
          -- show it reduces to swap d c • RHS. Then argue swap d c fixes
          -- the RHS via `fv_subst_subset_tight`.
          --
          -- Case split on `d ∈ σ.codSupp` vs `d ∉ σ.codSupp`.
          by_cases hd_cs : d ∈ σ.codSupp
          · -- Case d ∈ σ.codSupp: this is the last remaining obstacle. The
            -- issue is that `swap d c • σ ≠ σ`, so we cannot apply the
            -- direct `subst_perm` reduction used in the `d ∉ σ.codSupp`
            -- branch. Several equivalent reductions all end up requiring
            -- either `d ∉ σ.codSupp` or induction on a permuted subterm
            -- (`swap d c • t'`), which structural induction on `t'` does
            -- not provide.
            --
            -- Resolution routes worth pursuing:
            --   (a) Strong induction on `sizeOf t`, since permutation
            --       preserves size and IH would then apply to
            --       `swap d f • t'` for a fresh `f`.
            --   (b) Mutual induction of `subst_swap` with the α-renaming
            --       lemma `subst σ (lam d t') = subst σ (lam f (swap d f • t'))`
            --       for `f ∉ fv t'`.
            --   (c) An α-preserving substitution normalisation on `σ` that
            --       ensures every substitution used in the induction has
            --       its supp disjoint from binders inside the body.
            --
            -- Deferred here as it requires infrastructure beyond the
            -- current scope. In practice, subst_swap is always invoked
            -- from `subst_alpha` at the top-level with a σ whose codSupp
            -- may contain `d` but where the shadowing is handled by the
            -- inner freshBinder rewrites.
            sorry
          · -- Case d ∉ σ.codSupp: `swap d c` fixes σ, so we can push the
            -- swap through via `subst_perm` and land back on the RHS.
            have hswap_σ : swap d c • σ = σ :=
              Subst.swap_smul_eq_self_of_notMem_codSupp σ hd_cs hc_cs
            -- Apply subst_perm to LHS body with π := swap d c.
            have hpermLHS : (swap d c : Perm)
                • subst (σ.update c (Lam.var e)) (swap d c • t')
              = subst (σ.update d (Lam.var e)) t' := by
              rw [subst_perm]
              -- Compute swap d c • (σ.update c (Lam.var e)).
              rw [Subst.smul_update, hswap_σ]
              -- Now goal: subst (σ.update (swap d c • c) (swap d c • Lam.var e))
              --             (swap d c • swap d c • t')
              --   = subst (σ.update d (Lam.var e)) t'.
              have hcc : (swap d c : Perm) • c = d := by
                change Equiv.swap d c c = d
                exact Equiv.swap_apply_right d c
              have hee : (swap d c : Perm) • Lam.var e = Lam.var e := by
                rw [Lam.smul_var]
                congr 1
                change Equiv.swap d c e = e
                exact Equiv.swap_apply_of_ne_of_ne hed hec
              rw [hcc, hee, ← mul_smul, Equiv.swap_mul_self, one_smul]
            -- Now show LHS body = swap d c • LHS body by proving swap d c
            -- fixes the RHS body (via fv_subst_subset_tight).
            have hRHS_fv_no_d : d ∉ Lam.fv (subst (σ.update d (Lam.var e)) t') := by
              intro hin
              have hbi := fv_subst_subset_tight (σ.update d (Lam.var e)) t' hin
              rw [Finset.mem_biUnion] at hbi
              obtain ⟨x, hxfv, hxin⟩ := hbi
              change d ∈ Lam.fv (Function.update σ.toFun d (Lam.var e) x) at hxin
              by_cases hxd : x = d
              · rw [hxd, Function.update_self] at hxin
                change d ∈ ({e} : Finset Atom) at hxin
                rw [Finset.mem_singleton] at hxin
                exact hed hxin.symm
              · rw [Function.update_of_ne hxd] at hxin
                -- d ∈ Lam.fv (σ.toFun x). Need d ∈ σ.codSupp.
                by_cases hxs : x ∈ σ.supp
                · exact hd_cs (Finset.mem_union.mpr (Or.inr
                    (Finset.mem_biUnion.mpr ⟨x, hxs, hxin⟩)))
                · -- x ∉ σ.supp, so σ.toFun x = Lam.var x. fv = {x}. d = x.
                  rw [σ.outside_id x hxs] at hxin
                  change d ∈ ({x} : Finset Atom) at hxin
                  rw [Finset.mem_singleton] at hxin
                  exact hxd hxin.symm
            have hRHS_fv_no_c : c ∉ Lam.fv (subst (σ.update d (Lam.var e)) t') := by
              intro hin
              have hbi := fv_subst_subset_tight (σ.update d (Lam.var e)) t' hin
              rw [Finset.mem_biUnion] at hbi
              obtain ⟨x, hxfv, hxin⟩ := hbi
              change c ∈ Lam.fv (Function.update σ.toFun d (Lam.var e) x) at hxin
              by_cases hxd : x = d
              · rw [hxd, Function.update_self] at hxin
                change c ∈ ({e} : Finset Atom) at hxin
                rw [Finset.mem_singleton] at hxin
                exact hec hxin.symm
              · rw [Function.update_of_ne hxd] at hxin
                by_cases hxs : x ∈ σ.supp
                · exact hc_cs (Finset.mem_union.mpr (Or.inr
                    (Finset.mem_biUnion.mpr ⟨x, hxs, hxin⟩)))
                · rw [σ.outside_id x hxs] at hxin
                  change c ∈ ({x} : Finset Atom) at hxin
                  rw [Finset.mem_singleton] at hxin
                  -- c = x. x ∈ fv t' ⊆ allAtoms t'. But c ∉ allAtoms t'.
                  have hcx : c ∈ fv t' := hxin ▸ hxfv
                  exact hct' (fv_subset_allAtoms t' hcx)
            have hfix_RHS : (swap d c : Perm)
                • subst (σ.update d (Lam.var e)) t'
              = subst (σ.update d (Lam.var e)) t' := by
              apply Lam.supports_fv
              intro a' ha'
              have had' : a' ≠ d := fun h => hRHS_fv_no_d (h ▸ ha')
              have hac' : a' ≠ c := fun h => hRHS_fv_no_c (h ▸ ha')
              change Equiv.swap d c a' = a'
              exact Equiv.swap_apply_of_ne_of_ne had' hac'
            -- Combine: swap d c • LHS body = RHS body = swap d c • RHS body.
            -- So LHS body = swap d c • swap d c • LHS body = swap d c • RHS body = RHS body.
            have : (swap d c : Perm) •
                subst (σ.update c (Lam.var e)) (swap d c • t')
              = (swap d c : Perm) • subst (σ.update d (Lam.var e)) t' := by
              rw [hpermLHS, hfix_RHS]
            have := congrArg ((swap d c : Perm) • ·) this
            simp only [← mul_smul, Equiv.swap_mul_self, one_smul] at this
            exact this
        · -- Case d ≠ a: swap a c • d = d (since d ≠ a and d ≠ c).
          have had_ne : d ≠ a := hda
          have hdc_ne : d ≠ c := Ne.symm hcd
          have hswap_d : swap a c • d = d := by
            change Equiv.swap a c d = d
            exact Equiv.swap_apply_of_ne_of_ne had_ne hdc_ne
          rw [hswap_d]
          -- LHS = subst σ (lam d (swap a c • t')). RHS = subst (σ.update a (Lam.var c)) (lam d t').
          obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
            (σ.codSupp ∪ allAtoms t' ∪ allAtoms (swap a c • t')
              ∪ ({a, c, d} : Finset Atom))
          have hecs : e ∉ σ.codSupp := fun h => he_prop
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl h))))))
          have het : e ∉ allAtoms t' := fun h => he_prop
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inr h))))))
          have heswap : e ∉ allAtoms (swap a c • t') := fun h => he_prop
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
          have he_atoms : e ∉ ({a, c, d} : Finset Atom) := fun h => he_prop
            (Finset.mem_union.mpr (Or.inr h))
          have hea : e ≠ a := fun h => he_atoms
            (h ▸ Finset.mem_insert_self _ _)
          have hec : e ≠ c := fun h => he_atoms
            (h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
          have hed : e ≠ d := fun h => he_atoms
            (h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton.mpr rfl)))))
          -- Rewrite LHS via freshBinder with e as binder.
          have hL_fresh : e ∉ σ.codSupp ∪ allAtoms (lam d (swap a c • t')) := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · exact hecs h
            · change e ∈ insert d (allAtoms (swap a c • t')) at h
              rcases Finset.mem_insert.mp h with h | h
              · exact hed h
              · exact heswap h
          rw [subst_lam_freshBinder σ d (swap a c • t') hL_fresh]
          -- Rewrite RHS via freshBinder.
          have hR_fresh : e ∉ (σ.update a (Lam.var c)).codSupp
              ∪ allAtoms (lam d t') := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · rcases Finset.mem_union.mp h with hsupp | hbi
              · rcases Finset.mem_insert.mp hsupp with heq | h'
                · exact hea heq
                · exact hecs (σ.supp_subset_codSupp h')
              · rw [Finset.mem_biUnion] at hbi
                obtain ⟨x, hx, hxfv⟩ := hbi
                change e ∈ Lam.fv (Function.update σ.toFun a (Lam.var c) x) at hxfv
                by_cases hxa : x = a
                · subst hxa
                  rw [Function.update_self] at hxfv
                  change e ∈ ({c} : Finset Atom) at hxfv
                  rw [Finset.mem_singleton] at hxfv
                  exact hec hxfv
                · rw [Function.update_of_ne hxa] at hxfv
                  rcases Finset.mem_insert.mp hx with heq | h'
                  · exact hxa heq
                  · exact hecs (Finset.mem_union.mpr (Or.inr
                      (Finset.mem_biUnion.mpr ⟨x, h', hxfv⟩)))
            · change e ∈ insert d (allAtoms t') at h
              rcases Finset.mem_insert.mp h with h | h
              · exact hed h
              · exact het h
          rw [subst_lam_freshBinder (σ.update a (Lam.var c)) d t' hR_fresh]
          -- Goal: Lam.lam e (subst (σ.update d (Lam.var e)) (swap a c • t'))
          --     = Lam.lam e (subst ((σ.update a (Lam.var c)).update d (Lam.var e)) t').
          congr 1
          -- Apply IH (subst_swap on t') with σ' := σ.update d (Lam.var e), a' := a, c' := c.
          -- Need c ∉ σ'.codSupp and c ∉ allAtoms t'.
          have hc_σ' : c ∉ (σ.update d (Lam.var e)).codSupp := by
            intro h
            rcases Finset.mem_union.mp h with hsupp | hbi
            · rcases Finset.mem_insert.mp hsupp with heq | h'
              · exact hcd heq
              · exact hc_cs (σ.supp_subset_codSupp h')
            · rw [Finset.mem_biUnion] at hbi
              obtain ⟨x, hx, hxfv⟩ := hbi
              change c ∈ Lam.fv (Function.update σ.toFun d (Lam.var e) x) at hxfv
              by_cases hxd : x = d
              · subst hxd
                rw [Function.update_self] at hxfv
                change c ∈ ({e} : Finset Atom) at hxfv
                rw [Finset.mem_singleton] at hxfv
                exact hec.symm hxfv
              · rw [Function.update_of_ne hxd] at hxfv
                rcases Finset.mem_insert.mp hx with heq | h'
                · exact hxd heq
                · exact hc_cs (Finset.mem_union.mpr (Or.inr
                    (Finset.mem_biUnion.mpr ⟨x, h', hxfv⟩)))
          have := ih (σ.update d (Lam.var e)) a c hc_σ' hct'
          -- this : subst (σ.update d (Lam.var e)) (swap a c • t')
          --      = subst ((σ.update d (Lam.var e)).update a (Lam.var c)) t'.
          rw [this]
          -- Goal: subst ((σ.update d (Lam.var e)).update a (Lam.var c)) t'
          --     = subst ((σ.update a (Lam.var c)).update d (Lam.var e)) t'.
          -- The two substitutions differ only in the order of updates at a and d.
          rw [Subst.update_update_comm σ hda (Lam.var e) (Lam.var c)]

/-! ### α-invariance of `RawLam.subst`

If `t` and `s` are α-equivalent raw terms, then `subst σ t = subst σ s`
as elements of `Lam`. The proof runs by induction on the derivation of
`AlphaEq`; the `lam` case bridges the different fresh-binder choices
via `subst_lam_freshBinder` and reduces the body equality to the
IH-provided `subst σ (swap a c • t) = subst σ (swap b c • s)` at a
fresh atom, using `subst_swap` to translate the swap into an
extended-substitution form. -/
theorem subst_alpha : ∀ {t s : RawLam} (σ : Subst),
    AlphaEq t s → subst σ t = subst σ s := by
  intro t s σ h
  induction h generalizing σ with
  | var a => rfl
  | app _ _ iht ihs =>
      change Lam.app (subst σ _) (subst σ _)
        = Lam.app (subst σ _) (subst σ _)
      rw [iht σ, ihs σ]
  | @lam a b t s L _ ih =>
      -- Pick e fresh for L, σ.codSupp, allAtoms t, allAtoms s, and {a, b}.
      obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
        (L ∪ σ.codSupp ∪ allAtoms t ∪ allAtoms s ∪ ({a, b} : Finset Atom))
      have heL : e ∉ L := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl h))))))))
      have hecs : e ∉ σ.codSupp := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr h))))))))
      have het : e ∉ allAtoms t := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr h))))))
      have hes : e ∉ allAtoms s := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
      have he_ab : e ∉ ({a, b} : Finset Atom) := fun h => he_prop
        (Finset.mem_union.mpr (Or.inr h))
      have hea : e ≠ a := fun h => he_ab
        (h ▸ Finset.mem_insert_self _ _)
      have heb : e ≠ b := fun h => he_ab
        (h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
      -- Rewrite LHS via freshBinder with binder e.
      have hL_fresh : e ∉ σ.codSupp ∪ allAtoms (lam a t) := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hecs h
        · change e ∈ insert a (allAtoms t) at h
          rcases Finset.mem_insert.mp h with h | h
          · exact hea h
          · exact het h
      rw [subst_lam_freshBinder σ a t hL_fresh]
      have hR_fresh : e ∉ σ.codSupp ∪ allAtoms (lam b s) := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hecs h
        · change e ∈ insert b (allAtoms s) at h
          rcases Finset.mem_insert.mp h with h | h
          · exact heb h
          · exact hes h
      rw [subst_lam_freshBinder σ b s hR_fresh]
      -- Now: Lam.lam e (subst (σ.update a (Lam.var e)) t)
      --    = Lam.lam e (subst (σ.update b (Lam.var e)) s).
      congr 1
      -- Apply IH at e: subst σ (swap a e • t) = subst σ (swap b e • s).
      have hIH := ih e heL σ
      -- Transform LHS body via subst_swap.
      rw [← subst_swap σ a e t hecs het, ← subst_swap σ b e s hecs hes]
      exact hIH

end RawLam

/-! ### Substitution on the α-quotient

Lifted from `RawLam.subst` via `Quotient.lift` using
`RawLam.subst_alpha`. This is the second-order substitution operation
of the paper (Def. 12 applied to relations). -/

/-- Substitution on the α-quotient. -/
def Lam.subst (σ : Subst) : Lam → Lam :=
  Quotient.lift (RawLam.subst σ) (fun _ _ h => RawLam.subst_alpha σ h)

@[simp] theorem Lam.subst_mk (σ : Subst) (t : RawLam) :
    Lam.subst σ (Lam.mk t) = RawLam.subst σ t := rfl

@[simp] theorem Lam.subst_var (σ : Subst) (x : Atom) :
    Lam.subst σ (Lam.var x) = σ x := rfl

@[simp] theorem Lam.subst_app (σ : Subst) (u v : Lam) :
    Lam.subst σ (Lam.app u v) = Lam.app (Lam.subst σ u) (Lam.subst σ v) := by
  refine Quotient.inductionOn₂ u v ?_
  intro _ _; rfl

/-- Equivariance of `Lam.subst`: `π • Lam.subst σ u = Lam.subst (π • σ) (π • u)`.
Follows immediately from the raw-level equivariance `RawLam.subst_perm`
by descending through the α-quotient with `Quotient.inductionOn`. -/
theorem Lam.subst_smul (π : Perm) (σ : Subst) (u : Lam) :
    π • Lam.subst σ u = Lam.subst (π • σ) (π • u) := by
  refine Quotient.inductionOn u ?_
  intro t
  change π • RawLam.subst σ t = RawLam.subst (π • σ) (π • t)
  exact RawLam.subst_perm σ π t

/-! ### Substitution by identity -/

/-- Substitution by the identity is the identity. -/
theorem Lam.subst_id (u : Lam) : Lam.subst Subst.id u = u := by
  have hid_cs : (Subst.id.codSupp : Finset Atom) = ∅ := by
    change Subst.id.supp ∪ Subst.id.supp.biUnion _ = ∅
    change ∅ ∪ Finset.biUnion ∅ _ = ∅
    rw [Finset.biUnion_empty, Finset.empty_union]
  have hid_notMem : ∀ (x : Atom), x ∉ (Subst.id.codSupp : Finset Atom) := by
    intro x; rw [hid_cs]; exact Finset.notMem_empty x
  refine Quotient.inductionOn u ?_
  intro t
  induction t with
  | var x =>
      change RawLam.subst Subst.id (RawLam.var x) = Lam.mk (RawLam.var x)
      rfl
  | app t s iht ihs =>
      change Lam.app (Lam.subst Subst.id (Lam.mk t)) (Lam.subst Subst.id (Lam.mk s))
        = Lam.mk (RawLam.app t s)
      have iht' : Lam.subst Subst.id (Lam.mk t) = Lam.mk t := iht
      have ihs' : Lam.subst Subst.id (Lam.mk s) = Lam.mk s := ihs
      rw [iht', ihs']
      rfl
  | lam d t ih =>
      obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
        (RawLam.allAtoms (RawLam.lam d t))
      have he_union : e ∉ Subst.id.codSupp ∪ RawLam.allAtoms (RawLam.lam d t) := by
        rw [hid_cs, Finset.empty_union]; exact he_prop
      have he_t : e ∉ RawLam.allAtoms t := fun h => he_prop
        (Finset.mem_insert_of_mem h)
      change RawLam.subst Subst.id (RawLam.lam d t) = Lam.mk (RawLam.lam d t)
      rw [RawLam.subst_lam_freshBinder Subst.id d t he_union]
      rw [← RawLam.subst_swap Subst.id d e t (hid_notMem e) he_t]
      have hid_swap : (swap d e : Perm) • Subst.id = Subst.id :=
        Subst.swap_smul_eq_self_of_notMem_codSupp Subst.id
          (hid_notMem d) (hid_notMem e)
      have hstep : RawLam.subst Subst.id ((swap d e : Perm) • t)
          = (swap d e : Perm) • RawLam.subst Subst.id t := by
        rw [RawLam.subst_perm, hid_swap]
      rw [hstep]
      have ih' : RawLam.subst Subst.id t = Lam.mk t := ih
      rw [ih']
      have he_fv : e ∉ Lam.fv (Lam.mk t) := by
        change e ∉ RawLam.fv t
        exact fun h => he_t (RawLam.fv_subset_allAtoms t h)
      show Lam.lam e ((swap d e : Perm) • Lam.mk t) = Lam.lam d (Lam.mk t)
      exact (Lam.lam_alpha d e (Lam.mk t) (Or.inl he_fv)).symm

/-! ### `Lam`-level fresh binder rewrite -/

/-- Fresh-atom form of substitution on a `Lam.lam`. Requires `e ≠ a`. -/
theorem Lam.subst_lam_fresh (σ : Subst) (a : Atom) (u : Lam) {e : Atom}
    (he_cs : e ∉ σ.codSupp) (he_fv : e ∉ Lam.fv (Lam.lam a u))
    (he_ne : e ≠ a) :
    Lam.subst σ (Lam.lam a u)
      = Lam.lam e (Lam.subst (σ.update a (Lam.var e)) u) := by
  revert he_fv
  refine Quotient.inductionOn u ?_
  intro t' he_fv
  obtain ⟨e', he'_prop⟩ := LeanTra.Nominal.exists_notMem
    (σ.codSupp ∪ RawLam.allAtoms (RawLam.lam a t') ∪ {e})
  have he'cs : e' ∉ σ.codSupp := fun h => he'_prop
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h))))
  have he'a_lam : e' ∉ RawLam.allAtoms (RawLam.lam a t') := fun h => he'_prop
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
  have he'e : e' ≠ e := fun h => he'_prop
    (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr h)))
  have he'_a : e' ≠ a := fun h => he'a_lam
    (h ▸ Finset.mem_insert_self _ _)
  have he'_t : e' ∉ RawLam.allAtoms t' := fun h => he'a_lam
    (Finset.mem_insert_of_mem h)
  have he'_union : e' ∉ σ.codSupp ∪ RawLam.allAtoms (RawLam.lam a t') := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact he'cs h
    · exact he'a_lam h
  have he_fv_t' : e ∉ RawLam.fv t' \ {a} := by
    intro h
    apply he_fv
    show e ∈ Lam.fv (Lam.lam a (Lam.mk t'))
    rw [Lam.fv_lam, Lam.fv_mk]
    exact h
  show RawLam.subst σ (RawLam.lam a t')
    = Lam.lam e (Lam.subst (σ.update a (Lam.var e)) (Lam.mk t'))
  rw [RawLam.subst_lam_freshBinder σ a t' he'_union]
  change Lam.lam e' (RawLam.subst (σ.update a (Lam.var e')) t')
    = Lam.lam e (RawLam.subst (σ.update a (Lam.var e)) t')
  set X : Lam := RawLam.subst (σ.update a (Lam.var e')) t' with hX_def
  have he_notMem_X : e ∉ Lam.fv X := by
    intro hin
    have hbi := RawLam.fv_subst_subset_tight (σ.update a (Lam.var e')) t' hin
    rw [Finset.mem_biUnion] at hbi
    obtain ⟨x, hxfv, hxin⟩ := hbi
    change e ∈ Lam.fv (Function.update σ.toFun a (Lam.var e') x) at hxin
    by_cases hxa : x = a
    · rw [hxa, Function.update_self] at hxin
      change e ∈ ({e'} : Finset Atom) at hxin
      rw [Finset.mem_singleton] at hxin
      exact he'e.symm hxin
    · rw [Function.update_of_ne hxa] at hxin
      by_cases hxs : x ∈ σ.supp
      · exact he_cs (Finset.mem_union.mpr (Or.inr
          (Finset.mem_biUnion.mpr ⟨x, hxs, hxin⟩)))
      · rw [σ.outside_id x hxs] at hxin
        change e ∈ ({x} : Finset Atom) at hxin
        rw [Finset.mem_singleton] at hxin
        subst hxin
        exact he_fv_t' (Finset.mem_sdiff.mpr ⟨hxfv,
          fun h => hxa (Finset.mem_singleton.mp h)⟩)
  rw [Lam.lam_alpha e' e X (Or.inl he_notMem_X)]
  congr 1
  rw [hX_def]
  change (swap e' e : Perm) • Lam.subst (σ.update a (Lam.var e')) (Lam.mk t')
    = Lam.subst (σ.update a (Lam.var e)) (Lam.mk t')
  rw [Lam.subst_smul, Subst.smul_update]
  rw [Subst.swap_smul_eq_self_of_notMem_codSupp σ he'cs he_cs]
  have hswap_a : (swap e' e : Perm) • a = a := by
    change Equiv.swap e' e a = a
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm he'_a) (Ne.symm he_ne)
  rw [hswap_a]
  have hswap_var : (swap e' e : Perm) • Lam.var e' = Lam.var e := by
    rw [Lam.smul_var]
    congr 1
    change Equiv.swap e' e e' = e
    exact Equiv.swap_apply_left e' e
  rw [hswap_var]
  congr 1
  apply Lam.supports_fv
  intro y hy
  change Equiv.swap e' e y = y
  change y ∈ RawLam.fv t' at hy
  have hy_e' : y ≠ e' := fun h =>
    he'_t (h ▸ RawLam.fv_subset_allAtoms t' hy)
  have hy_ne_e : y ≠ e := by
    intro h; subst h
    exact he_fv_t' (Finset.mem_sdiff.mpr
      ⟨hy, fun hya => he_ne (Finset.mem_singleton.mp hya)⟩)
  exact Equiv.swap_apply_of_ne_of_ne hy_e' hy_ne_e

/-! ### Extensionality of substitution -/

/-- Substitution respects pointwise equality on the free variables. -/
theorem Lam.subst_ext {σ₁ σ₂ : Subst} (u : Lam)
    (h : ∀ x ∈ Lam.fv u, σ₁.toFun x = σ₂.toFun x) :
    Lam.subst σ₁ u = Lam.subst σ₂ u := by
  suffices h' : ∀ (t : RawLam) (σ₁ σ₂ : Subst),
      (∀ x ∈ RawLam.fv t, σ₁.toFun x = σ₂.toFun x) →
      Lam.subst σ₁ (Lam.mk t) = Lam.subst σ₂ (Lam.mk t) by
    revert h
    refine Quotient.inductionOn u ?_
    intro t hh
    exact h' t σ₁ σ₂ hh
  intro t
  induction t with
  | var x =>
      intro σ₁ σ₂ h
      change σ₁.toFun x = σ₂.toFun x
      exact h x (Finset.mem_singleton.mpr rfl)
  | app t s iht ihs =>
      intro σ₁ σ₂ h
      change Lam.app (Lam.subst σ₁ (Lam.mk t)) (Lam.subst σ₁ (Lam.mk s))
        = Lam.app (Lam.subst σ₂ (Lam.mk t)) (Lam.subst σ₂ (Lam.mk s))
      have ht : ∀ x ∈ RawLam.fv t, σ₁.toFun x = σ₂.toFun x := fun x hx =>
        h x (Finset.mem_union.mpr (Or.inl hx))
      have hs : ∀ x ∈ RawLam.fv s, σ₁.toFun x = σ₂.toFun x := fun x hx =>
        h x (Finset.mem_union.mpr (Or.inr hx))
      rw [iht σ₁ σ₂ ht, ihs σ₁ σ₂ hs]
  | lam d t ih =>
      intro σ₁ σ₂ h
      obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
        (σ₁.codSupp ∪ σ₂.codSupp ∪ RawLam.allAtoms (RawLam.lam d t))
      have he_1 : e ∉ σ₁.codSupp := fun hh => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hh))))
      have he_2 : e ∉ σ₂.codSupp := fun hh => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hh))))
      have he_all : e ∉ RawLam.allAtoms (RawLam.lam d t) := fun hh => he_prop
        (Finset.mem_union.mpr (Or.inr hh))
      have he_union1 : e ∉ σ₁.codSupp ∪ RawLam.allAtoms (RawLam.lam d t) := by
        intro hh; rcases Finset.mem_union.mp hh with hh | hh
        · exact he_1 hh
        · exact he_all hh
      have he_union2 : e ∉ σ₂.codSupp ∪ RawLam.allAtoms (RawLam.lam d t) := by
        intro hh; rcases Finset.mem_union.mp hh with hh | hh
        · exact he_2 hh
        · exact he_all hh
      change RawLam.subst σ₁ (RawLam.lam d t) = RawLam.subst σ₂ (RawLam.lam d t)
      rw [RawLam.subst_lam_freshBinder σ₁ d t he_union1]
      rw [RawLam.subst_lam_freshBinder σ₂ d t he_union2]
      congr 1
      apply ih
      intro x hx
      change Function.update σ₁.toFun d (Lam.var e) x
        = Function.update σ₂.toFun d (Lam.var e) x
      by_cases hxd : x = d
      · subst hxd
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
        apply h x
        exact Finset.mem_sdiff.mpr ⟨hx, fun hh => hxd (Finset.mem_singleton.mp hh)⟩

/-! ### Kleisli composition of substitutions -/

namespace Subst

/-- Kleisli composition: `(τ.comp σ) x = Lam.subst σ (τ x)`. -/
def comp (τ σ : Subst) : Subst where
  toFun := fun x => Lam.subst σ (τ.toFun x)
  supp := τ.supp ∪ σ.supp
  outside_id := by
    intro x hx
    rw [Finset.mem_union, not_or] at hx
    obtain ⟨hxτ, hxσ⟩ := hx
    rw [τ.outside_id x hxτ]
    change Lam.subst σ (Lam.var x) = Lam.var x
    rw [Lam.subst_var]
    exact σ.outside_id x hxσ

@[simp] theorem comp_apply (τ σ : Subst) (x : Atom) :
    (τ.comp σ).toFun x = Lam.subst σ (τ.toFun x) := rfl

end Subst

/-- Kleisli associativity of substitution. -/
theorem Lam.subst_comp (τ σ : Subst) (u : Lam) :
    Lam.subst (τ.comp σ) u = Lam.subst σ (Lam.subst τ u) := by
  refine Quotient.inductionOn u ?_
  intro t
  induction t generalizing τ σ with
  | var x =>
      change (τ.comp σ).toFun x = Lam.subst σ (τ.toFun x)
      rfl
  | app t s iht ihs =>
      change Lam.app (Lam.subst (τ.comp σ) (Lam.mk t)) (Lam.subst (τ.comp σ) (Lam.mk s))
        = Lam.subst σ (Lam.app (Lam.subst τ (Lam.mk t)) (Lam.subst τ (Lam.mk s)))
      rw [Lam.subst_app]
      congr 1
      · exact iht τ σ
      · exact ihs τ σ
  | lam d t ih =>
      obtain ⟨e, he_prop⟩ := LeanTra.Nominal.exists_notMem
        (τ.codSupp ∪ σ.codSupp ∪ (τ.comp σ).codSupp
          ∪ RawLam.allAtoms (RawLam.lam d t))
      have he_τ : e ∉ τ.codSupp := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl h))))))
      have he_σ : e ∉ σ.codSupp := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr h))))))
      have he_comp : e ∉ (τ.comp σ).codSupp := fun h => he_prop
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
      have he_all : e ∉ RawLam.allAtoms (RawLam.lam d t) := fun h => he_prop
        (Finset.mem_union.mpr (Or.inr h))
      have he_d : e ≠ d := fun h => he_all
        (h ▸ Finset.mem_insert_self _ _)
      have he_t : e ∉ RawLam.allAtoms t := fun h => he_all
        (Finset.mem_insert_of_mem h)
      have he_fv_t : e ∉ Lam.fv (Lam.mk t) := fun h => he_t
        (RawLam.fv_subset_allAtoms t h)
      have he_fv : e ∉ Lam.fv (Lam.lam d (Lam.mk t)) := by
        show e ∉ Lam.fv (Lam.mk t) \ {d}
        intro h; exact he_fv_t (Finset.mem_sdiff.mp h).1
      show Lam.subst (τ.comp σ) (Lam.lam d (Lam.mk t))
        = Lam.subst σ (Lam.subst τ (Lam.lam d (Lam.mk t)))
      rw [Lam.subst_lam_fresh (τ.comp σ) d (Lam.mk t) he_comp he_fv he_d]
      rw [Lam.subst_lam_fresh τ d (Lam.mk t) he_τ he_fv he_d]
      set X : Lam := Lam.subst (τ.update d (Lam.var e)) (Lam.mk t) with hX_def
      obtain ⟨f, hf_prop⟩ := LeanTra.Nominal.exists_notMem
        (σ.codSupp ∪ Lam.fv (Lam.lam e X) ∪ (τ.comp σ).codSupp
          ∪ RawLam.allAtoms (RawLam.lam d t) ∪ (τ.update d (Lam.var e)).codSupp
          ∪ Lam.fv X ∪ ({e, d} : Finset Atom))
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hf_prop
      obtain ⟨⟨⟨⟨⟨⟨hf_σ, hf_lamX⟩, hf_comp⟩, hf_lam_dt⟩, hf_τup⟩, _hf_X⟩, hf_e_or_d⟩ := hf_prop
      have hf_e : f ≠ e := fun h => hf_e_or_d.1 h
      have hf_d : f ≠ d := fun h => hf_e_or_d.2 h
      have hf_t_all : f ∉ RawLam.allAtoms t := fun h => hf_lam_dt
        (Finset.mem_insert_of_mem h)
      rw [Lam.subst_lam_fresh σ e X hf_σ hf_lamX hf_e]
      set σA : Subst := (τ.comp σ).update d (Lam.var e) with hσA_def
      have hf_σA_cs : f ∉ σA.codSupp := by
        intro h
        rcases Finset.mem_union.mp h with hsupp | hbi
        · rcases Finset.mem_insert.mp hsupp with heq | h'
          · exact hf_d heq
          · exact hf_comp (Finset.mem_union.mpr (Or.inl h'))
        · rw [Finset.mem_biUnion] at hbi
          obtain ⟨x, hx, hxfv⟩ := hbi
          change f ∈ Lam.fv (Function.update (τ.comp σ).toFun d (Lam.var e) x) at hxfv
          by_cases hxd : x = d
          · rw [hxd, Function.update_self] at hxfv
            change f ∈ ({e} : Finset Atom) at hxfv
            rw [Finset.mem_singleton] at hxfv
            exact hf_e hxfv
          · rw [Function.update_of_ne hxd] at hxfv
            rcases Finset.mem_insert.mp hx with heq | h'
            · exact hxd heq
            · exact hf_comp (Finset.mem_union.mpr (Or.inr
                (Finset.mem_biUnion.mpr ⟨x, h', hxfv⟩)))
      have hf_fv_A' : f ∉ Lam.fv (Lam.subst σA (Lam.mk t)) := by
        change f ∉ Lam.fv (RawLam.subst σA t)
        exact RawLam.fv_subst_notMem hf_σA_cs hf_t_all
      rw [Lam.lam_alpha e f (Lam.subst σA (Lam.mk t)) (Or.inl hf_fv_A')]
      congr 1
      rw [Lam.subst_smul]
      have hswap_t : (swap e f : Perm) • Lam.mk t = Lam.mk t := by
        apply Lam.supports_fv
        intro y hy
        change Equiv.swap e f y = y
        change y ∈ RawLam.fv t at hy
        have hye : y ≠ e := fun h => he_fv_t (h ▸ hy)
        have hyf : y ≠ f := fun h =>
          hf_t_all (h ▸ RawLam.fv_subset_allAtoms t hy)
        exact Equiv.swap_apply_of_ne_of_ne hye hyf
      rw [hswap_t]
      have hIH : Lam.subst
          ((τ.update d (Lam.var e)).comp (σ.update e (Lam.var f))) (Lam.mk t)
        = Lam.subst (σ.update e (Lam.var f))
            (Lam.subst (τ.update d (Lam.var e)) (Lam.mk t)) :=
        ih (τ.update d (Lam.var e)) (σ.update e (Lam.var f))
      show Lam.subst ((swap e f : Perm) • σA) (Lam.mk t)
        = Lam.subst (σ.update e (Lam.var f))
            (Lam.subst (τ.update d (Lam.var e)) (Lam.mk t))
      rw [← hIH]
      apply Lam.subst_ext
      intro x hx
      change x ∈ RawLam.fv t at hx
      have hxe : x ≠ e := fun h => he_fv_t (h ▸ hx)
      have hxf : x ≠ f := fun h =>
        hf_t_all (h ▸ RawLam.fv_subset_allAtoms t hx)
      have hswap_x : (swap e f : Perm)⁻¹ • x = x := by
        show (Equiv.swap e f).symm x = x
        rw [Equiv.symm_swap]
        exact Equiv.swap_apply_of_ne_of_ne hxe hxf
      change (swap e f : Perm) • σA.toFun ((swap e f : Perm)⁻¹ • x)
        = ((τ.update d (Lam.var e)).comp (σ.update e (Lam.var f))).toFun x
      rw [hswap_x]
      by_cases hxd : x = d
      · subst hxd
        show (swap e f : Perm) • Function.update (τ.comp σ).toFun x (Lam.var e) x
          = Lam.subst (σ.update e (Lam.var f)) (Function.update τ.toFun x (Lam.var e) x)
        rw [Function.update_self, Function.update_self, Lam.subst_var]
        change (swap e f : Perm) • (Lam.var e : Lam) = (σ.update e (Lam.var f)).toFun e
        rw [Subst.update_apply_same, Lam.smul_var]
        congr 1
        change Equiv.swap e f e = f
        exact Equiv.swap_apply_left e f
      · rw [Subst.update_apply_ne _ _ _ hxd]
        change (swap e f : Perm) • Lam.subst σ (τ.toFun x)
          = Lam.subst (σ.update e (Lam.var f)) ((τ.update d (Lam.var e)).toFun x)
        rw [Subst.update_apply_ne _ _ _ hxd]
        rw [Lam.subst_smul]
        rw [Subst.swap_smul_eq_self_of_notMem_codSupp σ he_σ hf_σ]
        have hswap_τx : (swap e f : Perm) • τ.toFun x = τ.toFun x := by
          apply Lam.supports_fv
          intro y hy
          change Equiv.swap e f y = y
          have hye : y ≠ e := by
            intro heq; subst heq
            by_cases hxs : x ∈ τ.supp
            · exact he_τ (Finset.mem_union.mpr (Or.inr
                (Finset.mem_biUnion.mpr ⟨x, hxs, hy⟩)))
            · rw [τ.outside_id x hxs] at hy
              change y ∈ ({x} : Finset Atom) at hy
              rw [Finset.mem_singleton] at hy
              subst hy; exact hxe rfl
          have hyf : y ≠ f := by
            intro heq; subst heq
            by_cases hxs : x ∈ τ.supp
            · exact hf_τup (Finset.mem_union.mpr (Or.inr
                (Finset.mem_biUnion.mpr ⟨x, Finset.mem_insert_of_mem hxs, by
                  change y ∈ Lam.fv (Function.update τ.toFun d (Lam.var e) x)
                  rw [Function.update_of_ne hxd]; exact hy⟩)))
            · rw [τ.outside_id x hxs] at hy
              change y ∈ ({x} : Finset Atom) at hy
              rw [Finset.mem_singleton] at hy
              subst hy; exact hxf rfl
          exact Equiv.swap_apply_of_ne_of_ne hye hyf
        rw [hswap_τx]
        apply Lam.subst_ext
        intro y hy
        have hye : y ≠ e := by
          intro heq; subst heq
          by_cases hxs : x ∈ τ.supp
          · exact he_τ (Finset.mem_union.mpr (Or.inr
              (Finset.mem_biUnion.mpr ⟨x, hxs, hy⟩)))
          · rw [τ.outside_id x hxs] at hy
            change y ∈ ({x} : Finset Atom) at hy
            rw [Finset.mem_singleton] at hy
            subst hy; exact hxe rfl
        rw [Subst.update_apply_ne _ _ _ hye]

end Named

end LeanTra.Instances.Lambda
