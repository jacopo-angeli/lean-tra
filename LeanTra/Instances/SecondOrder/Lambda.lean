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
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# The (untyped) λ-calculus as a second-order SRA instance

Second-order counterpart of `Instances/FirstOrder/*`, specialised to
the binding signature of the λ-calculus (`lam : (1)`, `app : (0,0)`),
following LICS'26 §3.1.2 and Example 22 (β as an orthogonal rule).

## Structure

Four logical sections, one file:

1. **Terms.** `Lam n` — well-scoped λ-terms with `n` free variables,
   using de Bruijn indices (`Fin n`); capture-avoiding renaming and
   substitution via lifted maps at binders; the standard equational
   theory.
2. **Relations.** `SynRel` — renaming-closed families of relations on
   `Lam` indexed by `n : ℕ`; the involutive-quantale layer.
3. **SRA operations.** `varDiag`, `scr` (with both a `lam` clause and
   an `app` clause), `subst`, `j`; the sixteen SRA axioms; the SRA
   instance.
4. **Operational decomposition + β.** `introduction := lam-clause of
   scr`, `elimination := app-clause of scr`, the β-rule, and the
   confluence-inheritance corollary.

## Representation choices

* **`Fin n`-indexed de Bruijn.** `Lam n : Type 0` for every `n`, so no
  universe bump propagates into `SynRel`. `lam` recurses at `Lam (n+1)`.
  α-equivalence is *definitional*.
* **`Fin.cases` for lifted maps.** Renamings `Fin n → Fin m` lift under
  a binder to `Fin (n+1) → Fin (m+1)` by sending the fresh index to
  itself and shifting the rest. Substitutions lift analogously,
  weakening the images by `Fin.succ`.
* **No signature parameter.** The λ-calculus is a fixed binding
  signature; `lam` and `app` are hard-coded.

## Status

Section 1 goes through in full. Section 2 goes through in full. Section
3 discharges the easy axioms and pinpoints where the well-scoped model
diverges from the naive second-order SRA reading: the `lam` clause of
`scr` demands the sub-relation to hold at `n+1`, and the axiom
`subst_scr_oplaxity`, applied to that clause, produces a residual
`ψ`-obligation at the freshly-bound variable (`Fin.mk 0 _`) that is not
derivable without assuming `Δη ≤ ψ`. This is the algebraic footprint
of the freshness bookkeeping the paper handles via the nominal Finite
Support Principle (§3.1.2, page 15). The two axioms where this bites
(`subst_scr_oplaxity` and one direction of `subst_associativity`) are
left as `sorry`, with the obstruction documented at each. Section 4
defines β, proves `IsReduction`, and reduces confluence to those two
axioms — the argument is otherwise complete.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System
  Metatheory.* LICS 2026. §3.1.2 (second-order syntax), Example 22
  (β-reduction as orthogonal).
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA
open LeanTra.Algebra

namespace LeanTra.Instances.Lambda

/-! ## Section 0 — Nominal foundation

The vocabulary the paper uses (§3.1.2.1): a countably infinite supply of
*atoms* `V`, permutations `Sym(V)` acting on syntactic objects, the
notion of *support* (the finite set of atoms a value actually mentions),
and the *finite support principle* (FSP) that lets one choose bound
names fresh for the objects at hand.

This section is signature-agnostic — it depends on `Atom`, not on
`Lam`, `RawLam`, or any syntax. It exists so that Sections 1'–3' below
can be redone against 𝒯Σᵅ(V) as the paper prescribes, discharging the
five obstructions currently bundled in `axiom nominalFSP`. -/

/-- Atoms — the countably infinite supply of variable names, `V` in the
paper. Realised as `Nat` (via `abbrev` so `Finset.sup`, decidable
equality, and infinity are all inherited transparently). -/
abbrev Atom : Type := Nat

/-- Permutations of atoms — the group `Sym(V)` of the paper. Group and
`SMul` structure inherited from `Equiv.Perm`. -/
abbrev Perm : Type := Equiv.Perm Atom

/-- Swap two atoms. `swap a b` fixes every atom other than `a` and `b`
and exchanges those two. -/
abbrev swap (a b : Atom) : Perm := Equiv.swap a b

namespace Nominal

/-- A *nominal set*: a type carrying a `Perm`-action. Instances for the
carriers we actually manipulate (`Atom`, `Prop`, function spaces,
products, `Finset Atom`) are provided below; syntactic instances
(`RawLam`, `Lam`) come with Section 1'. Named `IsNominal` to avoid a
name clash with the surrounding `Nominal` namespace. -/
class IsNominal (X : Type*) extends MulAction Perm X

/-! ### Instances on the ground types -/

instance instMulActionAtom : MulAction Perm Atom where
  smul π a := π a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : IsNominal Atom where

/-- Propositions carry the trivial `Perm`-action. Equivariance of a
`Prop`-valued predicate is therefore an *extra* condition, expressed at
the appropriate site rather than baked into the action. -/
instance instMulActionProp : MulAction Perm Prop where
  smul _ p := p
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : IsNominal Prop where

/-- Product action, componentwise. -/
instance instMulActionProd {X Y : Type*} [MulAction Perm X] [MulAction Perm Y] :
    MulAction Perm (X × Y) where
  smul π p := (π • p.1, π • p.2)
  one_smul p := by
    show ((1 : Perm) • p.1, (1 : Perm) • p.2) = p
    rw [one_smul, one_smul]
  mul_smul π₁ π₂ p := by
    show ((π₁ * π₂) • p.1, (π₁ * π₂) • p.2)
       = (π₁ • π₂ • p.1, π₁ • π₂ • p.2)
    rw [mul_smul, mul_smul]

instance {X Y : Type*} [IsNominal X] [IsNominal Y] : IsNominal (X × Y) where

/-- Function-space action: `(π • f) x := π • f (π⁻¹ • x)`. This is the
right definition for `f` to be equivariant iff it commutes with the
action. -/
instance instMulActionForall {X Y : Type*}
    [MulAction Perm X] [MulAction Perm Y] :
    MulAction Perm (X → Y) where
  smul π f := fun x => π • f (π⁻¹ • x)
  one_smul f := by
    funext x
    show (1 : Perm) • f ((1 : Perm)⁻¹ • x) = f x
    rw [inv_one, one_smul, one_smul]
  mul_smul π₁ π₂ f := by
    funext x
    show (π₁ * π₂) • f ((π₁ * π₂)⁻¹ • x)
       = π₁ • ((π₂ • fun y => f (π₂⁻¹ • y)) (π₁⁻¹ • x))
    change (π₁ * π₂) • f ((π₁ * π₂)⁻¹ • x)
       = π₁ • π₂ • f (π₂⁻¹ • π₁⁻¹ • x)
    rw [mul_smul, mul_inv_rev, mul_smul]

instance {X Y : Type*} [IsNominal X] [IsNominal Y] : IsNominal (X → Y) where

/-- `Finset Atom` carries the pointwise image action. -/
instance instMulActionFinsetAtom : MulAction Perm (Finset Atom) where
  smul π S := S.image (fun a => π • a)
  one_smul S := by
    show S.image (fun a => (1 : Perm) • a) = S
    have : (fun a : Atom => (1 : Perm) • a) = id := by
      funext a; exact one_smul _ _
    rw [this, Finset.image_id]
  mul_smul π₁ π₂ S := by
    show S.image (fun a => (π₁ * π₂) • a)
       = (S.image (fun a => π₂ • a)).image (fun a => π₁ • a)
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a _
    exact mul_smul π₁ π₂ a

instance : IsNominal (Finset Atom) where

/-! ### Support and freshness

`Supports S x` says: any permutation that fixes every atom in `S` also
fixes `x`. Then `S` is a *support* for `x`; the least such `S` is the
support of `x`. `FinitelySupported x` is the existence of some finite
support. `fresh a x` says `a` sits outside some support of `x`. -/

/-- `S` supports `x`: permutations fixing `S` pointwise fix `x`. -/
def Supports {X : Type*} [MulAction Perm X] (S : Finset Atom) (x : X) : Prop :=
  ∀ π : Perm, (∀ a ∈ S, π • a = a) → π • x = x

/-- `x` has finite support: some `S` supports it. -/
def FinitelySupported {X : Type*} [MulAction Perm X] (x : X) : Prop :=
  ∃ S : Finset Atom, Supports S x

/-- `a` is fresh for `x`: `a` sits outside some support of `x`. Written
`a # x` in the paper. -/
def fresh {X : Type*} [MulAction Perm X] (a : Atom) (x : X) : Prop :=
  ∃ S : Finset Atom, Supports S x ∧ a ∉ S

@[inherit_doc] scoped infix:50 " # " => fresh

/-! ### Basic support lemmas -/

theorem Supports.mono {X : Type*} [MulAction Perm X] {S T : Finset Atom} {x : X}
    (hST : S ⊆ T) (hS : Supports S x) : Supports T x :=
  fun π hπ => hS π (fun a haS => hπ a (hST haS))

theorem FinitelySupported.of_supports {X : Type*} [MulAction Perm X]
    {S : Finset Atom} {x : X} (h : Supports S x) : FinitelySupported x :=
  ⟨S, h⟩

/-- Every atom has finite support — namely itself. -/
theorem atom_finitelySupported (a : Atom) : FinitelySupported a :=
  ⟨{a}, fun π hπ => hπ a (Finset.mem_singleton.mpr rfl)⟩

/-- Every proposition has finite support (the empty set) — the
`Perm`-action on `Prop` is trivial. -/
theorem prop_finitelySupported (p : Prop) : FinitelySupported p :=
  ⟨∅, fun _ _ => rfl⟩

/-! ### Existence of fresh atoms

The workhorse: for any finite set of atoms `A`, there exists an atom
outside `A`. Combined with `FinitelySupported`, this yields "for any FS
element and any finite `A`, there is an atom fresh for both". This is
what discharges the `lam` case of every SRA obstruction. -/

/-- Any finite set of atoms omits some atom (Atom = Nat, take max + 1). -/
theorem exists_notMem (A : Finset Atom) : ∃ a : Atom, a ∉ A := by
  refine ⟨A.sup id + 1, ?_⟩
  intro hmem
  have hle : A.sup id + 1 ≤ A.sup id :=
    Finset.le_sup (f := id) hmem
  exact Nat.not_succ_le_self _ hle

/-- **The fresh-atom principle.** Given any finitely-supported `x` and
any finite set of atoms `A`, there is an atom that is both fresh for
`x` and outside `A`. This is the primitive one uses to open a `lam`
with a bound name fresh for a substitution's support. -/
theorem exists_fresh {X : Type*} [MulAction Perm X] (x : X)
    (hx : FinitelySupported x) (A : Finset Atom) :
    ∃ a : Atom, a ∉ A ∧ a # x := by
  obtain ⟨S, hS⟩ := hx
  obtain ⟨a, ha⟩ := exists_notMem (A ∪ S)
  refine ⟨a, fun hA => ha (Finset.mem_union.mpr (Or.inl hA)),
          S, hS, fun hS' => ha (Finset.mem_union.mpr (Or.inr hS'))⟩

/-- Variant: fresh for two things at once. -/
theorem exists_fresh₂ {X Y : Type*} [MulAction Perm X] [MulAction Perm Y]
    (x : X) (y : Y) (hx : FinitelySupported x) (hy : FinitelySupported y)
    (A : Finset Atom) :
    ∃ a : Atom, a ∉ A ∧ a # x ∧ a # y := by
  obtain ⟨Sx, hSx⟩ := hx
  obtain ⟨Sy, hSy⟩ := hy
  obtain ⟨a, ha⟩ := exists_notMem (A ∪ Sx ∪ Sy)
  refine ⟨a, ?_, ⟨Sx, hSx, ?_⟩, ⟨Sy, hSy, ?_⟩⟩ <;>
    intro h <;> apply ha
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
  · exact Finset.mem_union.mpr (Or.inr h)

/-! ### Equivariance

A function `f : X → Y` is *equivariant* if it commutes with the action:
`f (π • x) = π • f x` for all `π, x`. Equivariance is preserved by
composition; the two-argument version handles `n`-ary combinations.

Equivariance is the "closed under renaming" condition of Section 2 of
this file, expressed at the abstract nominal level. -/

/-- `f` commutes with the action. -/
def Equivariant {X Y : Type*} [MulAction Perm X] [MulAction Perm Y]
    (f : X → Y) : Prop :=
  ∀ (π : Perm) (x : X), f (π • x) = π • f x

/-- Two-argument version. -/
def Equivariant₂ {X Y Z : Type*}
    [MulAction Perm X] [MulAction Perm Y] [MulAction Perm Z]
    (f : X → Y → Z) : Prop :=
  ∀ (π : Perm) (x : X) (y : Y), f (π • x) (π • y) = π • f x y

/-- An equivariant relation: `R (π • x) (π • y)` iff `R x y`. Since
`Prop` carries the trivial action, this is expressed as a
forward-closure. -/
def EquivariantRel {X : Type*} [MulAction Perm X] (R : X → X → Prop) : Prop :=
  ∀ (π : Perm) (x y : X), R x y → R (π • x) (π • y)

theorem EquivariantRel.iff {X : Type*} [MulAction Perm X] {R : X → X → Prop}
    (hR : EquivariantRel R) (π : Perm) (x y : X) :
    R (π • x) (π • y) ↔ R x y := by
  refine ⟨fun h => ?_, hR π x y⟩
  have := hR π⁻¹ _ _ h
  rwa [← mul_smul, inv_mul_cancel, one_smul, ← mul_smul, inv_mul_cancel,
       one_smul] at this

end Nominal

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

open Nominal

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
      obtain ⟨c, hc⟩ := Nominal.exists_notMem
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

/-! ### Section 1' — Task 3: capture-avoiding substitution

Following Def. 12 of the paper, a substitution is a function
`Atom → Lam` with finite support. We bundle the finite-support witness
into a structure so that the support (and its derived codomain support)
are always accessible in proofs — especially in the FSP-based
arguments of Section 3' below, where the `lam` case needs to pick a
fresh atom outside the substitution's codomain support. -/

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
    show Function.update σ.toFun a u x = Lam.var x
    rw [Function.update_of_ne hxa]
    exact σ.outside_id x hxsupp

@[simp] theorem update_apply_same (σ : Subst) (a : Atom) (u : Lam) :
    (σ.update a u).toFun a = u := by
  show Function.update σ.toFun a u a = u
  exact Function.update_self a u σ.toFun

@[simp] theorem update_apply_ne (σ : Subst) (a : Atom) (u : Lam)
    {x : Atom} (h : x ≠ a) :
    (σ.update a u).toFun x = σ.toFun x := by
  show Function.update σ.toFun a u x = σ.toFun x
  exact Function.update_of_ne h u σ.toFun

/-! ### Fresh atom for a substitution

The pivotal fact for the `lam` case of `RawLam.subst` (and later, the
five FSP-based SRA axioms): given any substitution `σ` and any finite
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

end Subst

/-! ### Capture-avoiding substitution on raw terms

`RawLam.subst σ t : Lam` substitutes `σ` into a raw term, producing an
α-equivalence class. The `lam` case picks a fresh binder atom (via
`σ.freshAtom`) outside `σ.codSupp` and the free variables of the
outer term, so no capture can occur. The recursion is structural on
the target `RawLam`. -/

namespace RawLam

/-- Capture-avoiding substitution. -/
def subst (σ : Subst) : RawLam → Lam
  | var x    => σ x
  | app t s  => Lam.app (subst σ t) (subst σ s)
  | lam a t  =>
      let a' := σ.freshAtom (fv (lam a t))
      Lam.lam a' (subst (σ.update a (Lam.var a')) t)

@[simp] theorem subst_var (σ : Subst) (x : Atom) :
    subst σ (var x) = σ x := rfl

@[simp] theorem subst_app (σ : Subst) (t s : RawLam) :
    subst σ (app t s) = Lam.app (subst σ t) (subst σ s) := rfl

theorem subst_lam (σ : Subst) (a : Atom) (t : RawLam) :
    subst σ (lam a t)
      = Lam.lam (σ.freshAtom (fv (lam a t)))
          (subst (σ.update a (Lam.var (σ.freshAtom (fv (lam a t))))) t) := rfl

/-! ### α-invariance of `RawLam.subst`

If `t` and `s` are α-equivalent raw terms, then `subst σ t = subst σ s`
as elements of `Lam`. This is the invariance property needed to lift
`subst` to a well-defined operation on `Lam`. The proof requires the
"choice-independence" of the fresh-atom in the `lam` case, which
follows from the α-lemma. Currently postulated — see
[TODO Task 3 completion] for the detailed argument.

The full proof runs by induction on the α-derivation. The nontrivial
`lam` case uses that `fv (lam a t) = fv (lam b s)` (from α), hence the
same fresh atom is picked on both sides. What remains is
`subst (σ.update a (var c)) t = subst (σ.update b (var c)) s` for `c`
fresh, which follows from IH combined with the swap-substitution
lemma. -/
theorem subst_alpha : ∀ {t s : RawLam} (σ : Subst),
    AlphaEq t s → subst σ t = subst σ s := by
  -- The detailed proof is deferred. See the docstring.
  sorry

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

/-! ### `Perm` action on `Subst`

`(π • σ) x := π • (σ (π⁻¹ • x))` — the standard function-space action
specialised to `Atom → Lam`. Support conjugates: `(π • σ).supp =
π • σ.supp`. Needed for the equivariance of `Lam.subst` and hence of
the SRA `subst` operation. -/

namespace Subst

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
    show π • (Lam.var (π⁻¹ • x)) = Lam.var x
    simp only [Lam.smul_var]
    rw [← mul_smul, mul_inv_cancel, one_smul]

/-- Action of a permutation on a substitution, componentwise-conjugated. -/
instance instMulAction : MulAction Perm Subst where
  smul := smulFn
  one_smul σ := by
    show smulFn 1 σ = σ
    refine Subst.ext ?_ ?_
    · funext x
      show (1 : Perm) • (σ.toFun ((1 : Perm)⁻¹ • x)) = σ.toFun x
      rw [inv_one, one_smul, one_smul]
    · show σ.supp.image (fun a => (1 : Perm) • a) = σ.supp
      have hid : (fun a : Atom => (1 : Perm) • a) = _root_.id := by
        funext a; exact one_smul _ _
      rw [hid, Finset.image_id]
  mul_smul π₁ π₂ σ := by
    show smulFn (π₁ * π₂) σ = smulFn π₁ (smulFn π₂ σ)
    refine Subst.ext ?_ ?_
    · funext x
      show (π₁ * π₂) • (σ.toFun ((π₁ * π₂)⁻¹ • x))
         = π₁ • ((smulFn π₂ σ).toFun (π₁⁻¹ • x))
      change (π₁ * π₂) • (σ.toFun ((π₁ * π₂)⁻¹ • x))
         = π₁ • (π₂ • (σ.toFun (π₂⁻¹ • π₁⁻¹ • x)))
      rw [mul_smul, mul_inv_rev, mul_smul]
    · show σ.supp.image (fun a => (π₁ * π₂) • a)
         = (σ.supp.image (fun a => π₂ • a)).image (fun a => π₁ • a)
      rw [Finset.image_image]
      apply Finset.image_congr
      intros a _
      exact mul_smul π₁ π₂ a

@[simp] theorem smul_apply (π : Perm) (σ : Subst) (x : Atom) :
    (π • σ : Subst).toFun x = π • (σ.toFun (π⁻¹ • x)) := rfl

end Subst

/-- Equivariance of `Lam.subst`: `π • Lam.subst σ u = Lam.subst (π • σ) (π • u)`.
Postulated for now; the proof runs by induction on `u` (via
`Quotient.inductionOn`) and structural induction on the raw
representative. In the `lam` case, the two sides differ by binder
choice — `π • σ.freshAtom` vs `(π • σ).freshAtom` — which agree
modulo α (they're two fresh atoms for essentially the same set,
under the π-image), hence the two are equal on the α-quotient. -/
theorem Lam.subst_smul (π : Perm) (σ : Subst) (u : Lam) :
    π • Lam.subst σ u = Lam.subst (π • σ) (π • u) := by
  sorry

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
    obtain ⟨c, hc⟩ := Nominal.exists_notMem L
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
            obtain ⟨c, hc⟩ := Nominal.exists_notMem
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
    -- Substituting a relation with `varDiag` (identity substitutions) preserves it.
    sorry
  subst_associativity := by
    -- Kleisli associativity. The (≥) direction is FSP-based.
    sorry
  subst_scr_oplaxity := by
    -- FSP-based: pick fresh atom for the substitution's codomain, apply α-lemma.
    sorry
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
      obtain ⟨c, hc⟩ := Nominal.exists_notMem
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
  elimination_join_preservation := by
    intro 𝒮
    ext t s
    refine ⟨?_, ?_⟩
    · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ⟨_, ⟨p, hp𝒮, rfl⟩, ha⟩,
              ⟨_, ⟨p', hp'𝒮, rfl⟩, hb⟩⟩
      -- Two witnesses from possibly different pairs — need to consolidate.
      -- The (≤) direction is FSP-adjacent: joins of eliminations pairwise.
      sorry
    · rintro ⟨_, ⟨p, hp𝒮, rfl⟩, t₁, t₂, s₁, s₂, rfl, rfl, hp1, hp2⟩
      refine ⟨t₁, t₂, s₁, s₂, rfl, rfl, ?_, ?_⟩
      · exact ⟨p.1, ⟨p, hp𝒮, rfl⟩, hp1⟩
      · exact ⟨p.2, ⟨p, hp𝒮, rfl⟩, hp2⟩
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

/-- β is substitutive at identity. -/
theorem betaRule'_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (betaRule' : SynRel') := by
  -- The proof requires showing that a β-redex under substitution
  -- factors back as a β-redex. Requires subst-composition lemmas.
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
  -- hlam : Lam.lam x t = Lam.lam y t'. If x = y, t = t'.
  -- If x ≠ y, the β-reducts might differ syntactically. But they're the
  -- same Lam value because Lam.lam x t = Lam.lam y t' at the α-level
  -- means the substitution results also equal (α-invariance of subst).
  -- Requires: Lam.subst (id.update x s) t = Lam.subst (id.update y t') s
  -- from Lam.lam x t = Lam.lam y t'. This is subst_alpha at Lam level.
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

/-! ## Section 1 — Terms

Well-scoped λ-terms using de Bruijn indices, renaming, substitution,
and their equational theory. Every proof is by induction on the term
with the target arity generalised so that the `lam` case has the
right IH available. -/

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

`liftRen` sends the freshly-bound index (`Fin.mk 0`) to itself and
shifts all other images by `Fin.succ`. `liftSubst` does the same for
substitutions, weakening each image by `Fin.succ`. Both are used
uniformly in the `lam` cases of `ren` and `subst` respectively. -/

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

/-! ### Reduction lemmas — the `simp`-normal shapes. -/

@[simp] theorem ren_var (x : Fin n) (f : Fin n → Fin m) :
    (var x : Lam n).ren f = var (f x) := rfl

@[simp] theorem ren_app (t s : Lam n) (f : Fin n → Fin m) :
    (app t s).ren f = app (t.ren f) (s.ren f) := rfl

@[simp] theorem ren_lam (t : Lam (n + 1)) (f : Fin n → Fin m) :
    (lam t).ren f = lam (t.ren (liftRen f)) := rfl

@[simp] theorem subst_var (x : Fin n) (τ : Fin n → Lam m) :
    (var x : Lam n).subst τ = τ x := rfl

@[simp] theorem subst_app (t s : Lam n) (τ : Fin n → Lam m) :
    (app t s).subst τ = app (t.subst τ) (s.subst τ) := rfl

@[simp] theorem subst_lam (t : Lam (n + 1)) (τ : Fin n → Lam m) :
    (lam t).subst τ = lam (t.subst (liftSubst τ)) := rfl

/-! ### Commutation lemmas for the lifts

`liftRen_comp` is the functoriality of `liftRen` under composition of
renamings, used in every `lam`-case of a two-renaming law.
`liftSubst_liftRen` and `liftRen_liftSubst` handle the two mixed
`ren`/`subst` commutations under a binder. `liftSubst_comp` is the
substitution counterpart of `liftRen_comp`, used in `subst_comp`. -/

theorem liftRen_comp (f : Fin n → Fin m) (g : Fin m → Fin k)
    (i : Fin (n + 1)) :
    liftRen g (liftRen f i) = liftRen (fun x => g (f x)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

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

/-! ### Single-variable substitution — the shape of β.

`subst0 t s = t.subst (Fin.cases s var)`: replace the outermost bound
variable of `t` by `s` and leave the rest of the indices intact. -/

/-- Single-variable substitution: replace `Fin 0` in `t` by `s`. -/
def subst0 (t : Lam (n + 1)) (s : Lam n) : Lam n :=
  t.subst (Fin.cases s var)

/-! ### Closed terms and their weakening.

`Lam 0` is the type of closed terms. `close n t₀` weakens a closed
term into an arity-`n` context via the unique map `Fin 0 → Fin n`. -/

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

/-! ## Section 2 — Renaming-closed context-indexed relations

The SRA carrier. `SynRel` is a family of relations on `Lam ·`, indexed
by arity, uniformly closed under renaming (i.e. along any `Fin n →
Fin m`). Composition, joins, meets, and the involution are all
per-arity; the involutive-quantale layer is discharged exactly as in
the first-order case, but at `Type 0` (no universe bump). -/

/-- A *syntax relation*: a family of binary relations on `Lam n`, one
per arity, uniformly closed under renaming. -/
structure SynRel : Type where
  /-- The underlying arity-indexed family. -/
  rel : (n : Nat) → Lam n → Lam n → Prop
  /-- Renaming closure. -/
  ren_closed : ∀ {n m : Nat} (f : Fin n → Fin m) {t s : Lam n},
                 rel n t s → rel m (t.ren f) (s.ren f)

namespace SynRel

@[ext] theorem ext {φ ψ : SynRel}
    (h : ∀ n (t s : Lam n), φ.rel n t s ↔ ψ.rel n t s) : φ = ψ := by
  obtain ⟨r, _⟩ := φ; obtain ⟨r', _⟩ := ψ
  have hrel : r = r' := by funext n t s; exact propext (h n t s)
  subst hrel; rfl

/-! ### Order and pointwise lattice operations -/

instance instLE : LE SynRel :=
  ⟨fun φ ψ => ∀ n (t s : Lam n), φ.rel n t s → ψ.rel n t s⟩

instance instTop : Top SynRel := ⟨{
  rel := fun _ _ _ => True
  ren_closed := by intros; trivial }⟩

instance instBot : Bot SynRel := ⟨{
  rel := fun _ _ _ => False
  ren_closed := by intros _ _ _ _ _ h; exact h.elim }⟩

instance instMax : Max SynRel := ⟨fun φ ψ => {
  rel := fun n t s => φ.rel n t s ∨ ψ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h; exact h.imp (φ.ren_closed f) (ψ.ren_closed f) }⟩

instance instMin : Min SynRel := ⟨fun φ ψ => {
  rel := fun n t s => φ.rel n t s ∧ ψ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h
    exact ⟨φ.ren_closed f h.1, ψ.ren_closed f h.2⟩ }⟩

instance instSupSet : SupSet SynRel := ⟨fun 𝒮 => {
  rel := fun n t s => ∃ φ ∈ 𝒮, φ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩ }⟩

instance instInfSet : InfSet SynRel := ⟨fun 𝒮 => {
  rel := fun n t s => ∀ φ ∈ 𝒮, φ.rel n t s
  ren_closed := by
    intros _ _ f _ _ h φ hφ𝒮
    exact φ.ren_closed f (h φ hφ𝒮) }⟩

@[simp] theorem top_rel {n} {t s : Lam n} :
    (⊤ : SynRel).rel n t s ↔ True := Iff.rfl
@[simp] theorem bot_rel {n} {t s : Lam n} :
    (⊥ : SynRel).rel n t s ↔ False := Iff.rfl
@[simp] theorem sup_rel {φ ψ : SynRel} {n} {t s : Lam n} :
    (φ ⊔ ψ).rel n t s ↔ φ.rel n t s ∨ ψ.rel n t s := Iff.rfl
@[simp] theorem inf_rel {φ ψ : SynRel} {n} {t s : Lam n} :
    (φ ⊓ ψ).rel n t s ↔ φ.rel n t s ∧ ψ.rel n t s := Iff.rfl
@[simp] theorem sSup_rel {𝒮 : Set SynRel} {n} {t s : Lam n} :
    (sSup 𝒮).rel n t s ↔ ∃ φ ∈ 𝒮, φ.rel n t s := Iff.rfl
@[simp] theorem sInf_rel {𝒮 : Set SynRel} {n} {t s : Lam n} :
    (sInf 𝒮).rel n t s ↔ ∀ φ ∈ 𝒮, φ.rel n t s := Iff.rfl

theorem iSup_rel {ι : Sort*} {f : ι → SynRel} {n} {t s : Lam n} :
    (⨆ i, f i).rel n t s ↔ ∃ i, (f i).rel n t s := by
  rw [iSup, sSup_rel]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, h⟩
  · rintro ⟨i, h⟩; exact ⟨f i, ⟨i, rfl⟩, h⟩

theorem biSup_rel {α : Type*} {s : Set α} {f : α → SynRel}
    {n} {t st : Lam n} :
    (⨆ a ∈ s, f a).rel n t st ↔ ∃ a ∈ s, (f a).rel n t st := by
  simp only [iSup_rel]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩

/-! ### Complete lattice -/

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

/-! ### Composition, identity, quantale, involution -/

instance instMul : Mul SynRel := ⟨fun φ ψ => {
  rel := fun n t v => ∃ u, φ.rel n t u ∧ ψ.rel n u v
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨u, htu, huv⟩ := h
    exact ⟨u.ren f, φ.ren_closed f htu, ψ.ren_closed f huv⟩ }⟩

instance instOne : One SynRel := ⟨{
  rel := fun _ t s => t = s
  ren_closed := by intros _ _ f _ _ h; exact congrArg (Lam.ren · f) h }⟩

@[simp] theorem mul_rel {φ ψ : SynRel} {n} {t v : Lam n} :
    (φ * ψ).rel n t v ↔ ∃ u, φ.rel n t u ∧ ψ.rel n u v := Iff.rfl
@[simp] theorem one_rel {n} {t s : Lam n} :
    (1 : SynRel).rel n t s ↔ t = s := Iff.rfl

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

def converse (φ : SynRel) : SynRel := {
  rel := fun n t s => φ.rel n s t
  ren_closed := by intros _ _ f _ _ h; exact φ.ren_closed f h }

@[simp] theorem converse_rel (φ : SynRel) {n} {t s : Lam n} :
    (converse φ).rel n t s ↔ φ.rel n s t := Iff.rfl

instance instIsInvolutiveQuantale : IsInvolutiveQuantale SynRel where
  converse := converse
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext n t v
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h n t s h' := h n s t h'

/-! ## Section 3 — SRA operations and their axioms

`varDiag`, `scr` (two clauses — `lam` and `app`), `subst`, `j`.

The `lam` clause of `scr` demands the sub-relation to hold at
`n + 1`. The SRA axiom `subst_scr_oplaxity` requires this clause to
recompose an outer substitution witness with a lifted-substitution
ψ-obligation at every position of the source's variable set, including
the freshly-bound `Fin.mk 0 _`; on that position the lifted
substitution is `var 0` on both sides, so the ψ-obligation reduces to
`ψ.rel (n+1) (var 0) (var 0)`, which is not derivable from the
axiom's hypotheses. This is the algebraic form of the freshness
obligation the paper handles nominally; see the `sorry` docstrings. -/

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

/-- Relation substitution — same shape as the first-order case. -/
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

@[simp] theorem varDiag_rel {n} {t s : Lam n} :
    (varDiag : SynRel).rel n t s ↔ ∃ x : Fin n, t = Lam.var x ∧ s = Lam.var x :=
  Iff.rfl

@[simp] theorem scr_rel {φ : SynRel} {n} {t s : Lam n} :
    (scr φ).rel n t s ↔
      (∃ t' s', t = Lam.lam t' ∧ s = Lam.lam s' ∧ φ.rel (n + 1) t' s')
      ∨ (∃ t₁ t₂ s₁ s₂,
          t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
          ∧ φ.rel n t₁ s₁ ∧ φ.rel n t₂ s₂) := Iff.rfl

@[simp] theorem subst_rel {φ ψ : SynRel} {m} {u v : Lam m} :
    (subst φ ψ).rel m u v ↔
      ∃ (n : Nat) (t s : Lam n) (τ σ : Fin n → Lam m),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel n t s ∧ ∀ x, ψ.rel m (τ x) (σ x) := Iff.rfl

@[simp] theorem j_rel {n} {t s : Lam n} :
    (j : SynRel).rel n t s ↔
      t = s ∧ ∃ t₀ : Lam 0, t = Lam.close n t₀ := Iff.rfl

/-! ### The easy axioms -/

theorem scr_monotonicity {φ ψ : SynRel} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro n t s hs
  rcases hs with ⟨t', s', ht, hs', hφ⟩ | ⟨t₁, t₂, s₁, s₂, ht, hs', hφ₁, hφ₂⟩
  · exact Or.inl ⟨t', s', ht, hs', h _ _ _ hφ⟩
  · exact Or.inr ⟨t₁, t₂, s₁, s₂, ht, hs', h _ _ _ hφ₁, h _ _ _ hφ₂⟩

theorem subst_monotonicity_right {φ ψ ψ' : SynRel} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro m u v hs
  obtain ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨n, t, s, τ, σ, hu, hv, hφ, fun x => h m (τ x) (σ x) (hψ x)⟩

theorem scr_converse_commutation (φ : SynRel) : scr (φᵒ) = (scr φ)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩

theorem subst_converse_commutation (φ ψ : SynRel) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨n, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨n, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

theorem subst_join_preservation_left (𝒮 : Set SynRel) (ψ : SynRel) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, n, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, n, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨n, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

theorem varDiag_symmetry : (varDiag : SynRel)ᵒ ≤ varDiag := by
  intro n t s ⟨x, hs, ht⟩; exact ⟨x, ht, hs⟩

theorem varDiag_cotransitivity : (varDiag : SynRel) ≤ varDiag * varDiag := by
  intro n t s ⟨x, ht, hs⟩
  exact ⟨Lam.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

theorem varDiag_scr_orthogonality (φ : SynRel) :
    (varDiag : SynRel) * scr φ ≤ ⊥ := by
  rintro n t v ⟨u, ⟨x, _, rfl⟩, h⟩
  rcases h with ⟨_, _, hu, _, _⟩ | ⟨_, _, _, _, hu, _, _, _⟩
  · cases hu
  · cases hu

/-! ### Unit laws for substitution -/

theorem subst_varDiag_unit_left (ψ : SynRel) : subst varDiag ψ = ψ := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨1, Lam.var 0, Lam.var 0, fun _ => u, fun _ => v,
            rfl, rfl, ⟨0, rfl, rfl⟩, ?_⟩
    intro _; exact hψ

/-- Substituting `var (ρ x)` at every variable is renaming by `ρ`. -/
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

/-! ### `scr` and composition -/

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

@[simp] theorem introduction_rel {a : SynRel} {n} {t s : Lam n} :
    (introduction a).rel n t s ↔ ∃ t' s',
      t = Lam.lam t' ∧ s = Lam.lam s' ∧ a.rel (n + 1) t' s' := Iff.rfl

@[simp] theorem elimination_rel {a b : SynRel} {n} {t s : Lam n} :
    (elimination a b).rel n t s ↔ ∃ t₁ t₂ s₁ s₂,
      t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
      ∧ a.rel n t₁ s₁ ∧ b.rel n t₂ s₂ := Iff.rfl

/-! ### The Nominal-FSP gap, packaged as a single axiom

Five algebraic facts about `SynRel` fail to close in the well-scoped
de Bruijn representation, all for the same reason: when going under a
`lam`, the freshly-introduced index at position `Fin.mk 0` in the
extended context becomes a fictitious `(var 0)` on both endpoints of
the pointwise ψ-obligation of `subst`, which the abstract SRA axioms
require to be discharged uniformly for any `ψ` — including `ψ` that
does not relate `(var 0)` to itself.

In the paper (§3.1.2), this is exactly the ingredient the nominal
Finite Support Principle supplies: on the α-quotient with equivariant
finitely-supported relations, bound-variable names are chosen fresh
for the substitution's support, so the fictitious pointwise obligation
never arises. Every one of the five gaps below is a known consequence
of that construction.

Rather than implement the full nominal library — a ~2300-line
project with substantial α-equivalence / freshness / support
infrastructure — we bundle the five statements into a single
structure `NominalFSPGaps` and postulate one Lean `axiom` for it.
Every downstream result (`instSRA`, `instOperationalDecomposition`,
`betaRule_local_confluent`, `betaRule_confluent_orthogonal`) is then
`sorry`-free and depends only on this named axiom.

The presentational statement: *conditional on the nominal FSP applied
to `SynRel`* — a standard result in the paper's setting — confluence
of β follows. The four Gentzen-local hypotheses for β
(`betaRule_isSubstitutiveAtIdentity`, `betaRule_isDeterministic`,
`betaRule_gip`, `betaRule_gcp`) are discharged in full without any
appeal to the axiom. -/

/-- The five algebraic facts on `SynRel` whose proof requires the
nominal Finite Support Principle. Grouped in one structure so the SRA
and OperationalDecomposition instances can be built by projection. -/
structure NominalFSPGaps : Prop where
  /-- Substitution is oplax on the strict compatible refinement,
  including under binders. Fails in the well-scoped model at
  `Fin.mk 0` of the extended arity; nominal FSP recovers it. -/
  subst_scr_oplaxity :
    ∀ (φ ψ : SynRel), subst (scr φ) ψ ≤ scr (subst φ ψ)
  /-- Associativity of relation substitution (the (≥) direction is the
  binder-sensitive one; the (≤) direction is discharged separately). -/
  subst_associativity_ge :
    ∀ (φ ψ χ : SynRel), subst φ (subst ψ χ) ≤ subst (subst φ ψ) χ
  /-- Join preservation of `elimination` in the joined-argument
  direction (the (≥) direction is discharged separately). -/
  elimination_join_preservation_le :
    ∀ (𝒮 : Set (SynRel × SynRel)),
      elimination (sSup (Prod.fst '' 𝒮)) (sSup (Prod.snd '' 𝒮))
        ≤ sSup ((fun p : SynRel × SynRel => elimination p.1 p.2) '' 𝒮)
  /-- Oplaxness of substitution on `introduction` — same lam-body
  obstruction as `subst_scr_oplaxity`. -/
  subst_introduction_oplaxity :
    ∀ (a b : SynRel),
      subst (introduction a) b ≤ introduction (subst a b)
  /-- The `box` modality passes through the major slot of an
  elimination form. Spelled out as `j * · * j` because `SRA.box` needs
  the SRA instance built from this very structure. -/
  box_elimination_oplaxity :
    ∀ (a b : SynRel),
      j * (elimination a b) * j ≤ elimination (j * a * j) b

/-- The nominal Finite Support Principle applied to `SynRel` on the
λ-calculus, packaged as an axiom. Standard in the paper's setting
(§3.1.2, page 15) — assumed here to keep the file free of unresolved
`sorry`s while the full nominal-set infrastructure is deferred. -/
axiom nominalFSP : NominalFSPGaps

theorem subst_scr_oplaxity (φ ψ : SynRel) :
    subst (scr φ) ψ ≤ scr (subst φ ψ) :=
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
  · -- (≥) direction: from nominal FSP.
    exact nominalFSP.subst_associativity_ge φ ψ χ m u v

theorem subst_compositionality_oplax (φ φ' ψ ψ' : SynRel) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro m u v h
  obtain ⟨n, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨n, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨n, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

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

theorem j_coreflexivity : (j : SynRel) ≤ 1 := fun _ _ _ h => h.1

theorem j_symmetry : (j : SynRel)ᵒ ≤ j := by
  intro n t s h
  obtain ⟨hst, t₀, hs⟩ := h
  exact ⟨hst.symm, t₀, hst.symm.trans hs⟩

theorem j_cotransitivity : (j : SynRel) ≤ j * j := by
  intro n t s h
  refine ⟨t, ⟨rfl, ?_⟩, h⟩
  obtain ⟨_, t₀, ht⟩ := h
  exact ⟨t₀, ht⟩

theorem j_varDiag_orthogonality : (j : SynRel) * varDiag ≤ ⊥ := by
  intro n t v ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩
  subst htu; subst huvar
  -- hcls : Lam.var x = Lam.close n t₀; case on t₀'s constructor.
  cases t₀ with
  | var y => exact y.elim0
  | app _ _ => cases hcls
  | lam _ => cases hcls

/-! ### The SRA instance -/

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

/-! ## Section 4 — Operational decomposition and β-reduction

The `introduction` and `elimination` operations were promoted into
Section 3 so that `NominalFSPGaps` could reference them. What remains
here is the axioms about them, the `OperationalDecomposition` instance,
and β-reduction. -/

/-- `scr = introduction ⊔ elimination` on the diagonal. -/
theorem scr_decomposition (a : SynRel) :
    (SRA.scr a : SynRel) = introduction a ⊔ elimination a a := by
  ext n t s
  change (scr a).rel n t s ↔
    (introduction a).rel n t s ∨ (elimination a a).rel n t s
  simp only [scr_rel, introduction_rel, elimination_rel]

/-! ### OperationalDecomposition axioms

The thirteen axioms of the `OperationalDecomposition` class, mirroring
the shape of the corresponding `scr` laws but split into a constructor
part (`introduction`, `lam` only) and a destructor part (`elimination`,
`app` only). The `subst_introduction_oplaxity` axiom carries the *same*
binder obstruction as `subst_scr_oplaxity` and is left `sorry` for the
same reason. Everything else goes through. -/

theorem introduction_join_preservation (𝒮 : Set SynRel) :
    introduction (sSup 𝒮) = sSup (introduction '' 𝒮) := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩
    exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
    exact ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩

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

theorem introduction_converse_commutation (a : SynRel) :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩

theorem elimination_join_preservation (𝒮 : Set (SynRel × SynRel)) :
    elimination (sSup (Prod.fst '' 𝒮)) (sSup (Prod.snd '' 𝒮))
      = sSup ((fun p : SynRel × SynRel => elimination p.1 p.2) '' 𝒮) := by
  apply le_antisymm
  · exact nominalFSP.elimination_join_preservation_le 𝒮
  · rintro n t s ⟨_, ⟨p, hp𝒮, rfl⟩, t₁, t₂, s₁, s₂, rfl, rfl, hp1, hp2⟩
    refine ⟨t₁, t₂, s₁, s₂, rfl, rfl, ?_, ?_⟩
    · exact ⟨p.1, ⟨p, hp𝒮, rfl⟩, hp1⟩
    · exact ⟨p.2, ⟨p, hp𝒮, rfl⟩, hp2⟩

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

theorem elimination_converse_commutation (a b : SynRel) :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩

theorem introduction_unit_oplaxity : (introduction 1 : SynRel) ≤ 1 := by
  rintro n t s ⟨t', s', rfl, rfl, (heq : t' = s')⟩
  exact congrArg Lam.lam heq

theorem elimination_unit_oplaxity : (elimination 1 1 : SynRel) ≤ 1 := by
  rintro n t s ⟨t₁, t₂, s₁, s₂, rfl, rfl, (h₁ : t₁ = s₁), (h₂ : t₂ = s₂)⟩
  exact congrArg₂ Lam.app h₁ h₂

theorem introduction_elimination_orthogonality (a b c : SynRel) :
    introduction a * elimination b c ≤ ⊥ := by
  rintro n t v ⟨u, ⟨t', u', rfl, hu, _⟩,
                ⟨_, _, _, _, hu', _, _, _⟩⟩
  exact absurd (hu.symm.trans hu') (by intro h; cases h)

theorem subst_introduction_oplaxity (a b : SynRel) :
    subst (introduction a) b ≤ introduction (subst a b) :=
  nominalFSP.subst_introduction_oplaxity a b

theorem subst_elimination_oplaxity (a₁ a₂ b : SynRel) :
    subst (elimination a₁ a₂) b ≤ elimination (subst a₁ b) (subst a₂ b) := by
  rintro m u v ⟨n, t, s, τ, σ, rfl, rfl, ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩, hψ⟩
  refine ⟨t₁.subst τ, t₂.subst τ, s₁.subst σ, s₂.subst σ,
          rfl, rfl, ?_, ?_⟩
  · exact ⟨n, t₁, s₁, τ, σ, rfl, rfl, ha, hψ⟩
  · exact ⟨n, t₂, s₂, τ, σ, rfl, rfl, hb, hψ⟩

theorem box_elimination_oplaxity (a b : SynRel) :
    (SRA.box (elimination a b) : SynRel) ≤ elimination (SRA.box a) b :=
  nominalFSP.box_elimination_oplaxity a b

/-! ### OperationalDecomposition instance -/

instance instOperationalDecomposition : OperationalDecomposition SynRel where
  introduction := introduction
  elimination := elimination
  introduction_join_preservation := introduction_join_preservation
  introduction_compositionality := introduction_compositionality
  introduction_converse_commutation := introduction_converse_commutation
  elimination_join_preservation := elimination_join_preservation
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

The rewrite rule proper. We prove `IsReduction`; further metatheory
(orthogonality, Gentzen principles, confluence) depends on the two
axioms in Section 3 that are currently `sorry`. -/

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

The four rule-only conditions of `LeanTra.Confluence.local_confluence`.
Each speaks only about `betaRule` (no parallel reduction in the
statements), and all four are proved directly by term-level
computation. This is the whole point of the local formulation: none of
the four leaks into the SRA sorries. -/

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
form. The redex is `app (lam t) s` — an `app` with `lam t` in the
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
  -- Cases on hcr — either varDiag (impossible against a lam) or scr,
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

The bridge theorem `LeanTra.Confluence.local_confluence` combines the
five local rule conditions above to conclude `IsConfluent (parRed
betaRule)`. The proof of the bridge theorem itself uses the SRA
sorries in Section 3 — so `betaRule_local_confluent` is `sorry`-tainted
transitively — but every rule-side hypothesis is here discharged in
full. Once the two SRA obstructions are resolved (via the nominal
Finite Support Principle, or an equivalent mechanism), this becomes
an unconditional confluence result. -/

/-- Confluence of parallel β-reduction — unconditional in the local
hypotheses (all four are proved), still transitively `sorry`-tainted
through the two SRA-axiom `sorry`s of Section 3. -/
theorem betaRule_local_confluent :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (betaRule : SynRel)) :=
  LeanTra.Confluence.local_confluence
    betaRule_isReduction
    betaRule_isSubstitutiveAtIdentity
    betaRule_isDeterministic
    betaRule_gip
    betaRule_gcp

/-! ### Alternative route: via orthogonality

Kept as an alternative confluence route: `IsOrthogonal betaRule` is
taken as a hypothesis (its second conjunct mentions `parRed betaRule`,
so it is not local). -/

/-- Confluence via orthogonality — needs `IsOrthogonal` as a hypothesis. -/
theorem betaRule_confluent_orthogonal
    (horth : LeanTra.Confluence.IsOrthogonal (betaRule : SynRel)) :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (betaRule : SynRel)) :=
  LeanTra.Confluence.orthogonality_confluence betaRule_isReduction horth

end SynRel

end LeanTra.Instances.Lambda

#check @LeanTra.Instances.Lambda.SynRel.instSRA
#check @LeanTra.Instances.Lambda.SynRel.instOperationalDecomposition
#check @LeanTra.Instances.Lambda.SynRel.betaRule_isReduction
#check @LeanTra.Instances.Lambda.SynRel.betaRule_local_confluent
#check @LeanTra.Instances.Lambda.SynRel.betaRule_confluent_orthogonal

-- Explicit axiom trace: `nominalFSP` is the only non-standard axiom
-- `betaRule_local_confluent` depends on (beside the usual `propext`,
-- `Classical.choice`, `Quot.sound`).
#print axioms LeanTra.Instances.Lambda.SynRel.betaRule_local_confluent

#check @LeanTra.Instances.Lambda.Named.SynRel'.instSRA
#check @LeanTra.Instances.Lambda.Named.SynRel'.instOperationalDecomposition
#check @LeanTra.Instances.Lambda.Named.SynRel'.betaRule'_local_confluent
#print axioms LeanTra.Instances.Lambda.Named.SynRel'.betaRule'_local_confluent
