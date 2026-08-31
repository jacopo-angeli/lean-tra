/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# Nominal sets

A **nominal set** is a mathematical structure for reasoning about
names and binding without the syntactic bureaucracy of de Bruijn
indices or the informal hand-waving of Barendregt's variable
convention. It packages three ingredients that together make
freshness a first-class notion:

1. A countably infinite set `V` of **atoms** — the primitive names
   over which everything is parameterised. Atoms have no internal
   structure; the only operation on them is comparison and
   permutation.

2. A group action of the symmetric group `Sym(V)` — **permutations**
   of atoms — on the carrier set `X`. Given a permutation `π` and an
   element `x : X`, applying `π` renames every atom occurrence inside
   `x` uniformly. The action satisfies the usual monoid laws
   (`1 • x = x` and `(π₁ * π₂) • x = π₁ • (π₂ • x)`).

3. A **finite-support** condition on each element: for every `x`
   there exists a finite set `S ⊆ V` such that any permutation
   fixing `S` pointwise also fixes `x`. Intuitively, `S` is "the
   atoms `x` actually depends on"; permutations that only shuffle
   atoms outside `S` cannot detect anything about `x`.

From these ingredients one derives:

* The notion of **support** `supp x` — the smallest such `S`.
* **Freshness** `a # x` — `a` is not in the support of `x`, i.e.
  `x` doesn't mention `a`.
* The **Choose-a-Fresh-Name Principle** (Pitts, *Nominal Sets*,
  Ch. 3): for any finitely-supported `x` and any finite `A ⊆ V`,
  there is an atom outside `A` that is fresh for `x`. This is the
  workhorse of nominal reasoning — every time an argument needs a
  "sufficiently fresh name" for a bound variable, this principle
  supplies one. (Not to be confused with Pitts's *Finite Support
  Principle*, which is a meta-theorem stating that objects defined
  from finitely-supported data in classical higher-order logic are
  themselves finitely supported. We do not formalise that principle
  as such; we use its instances directly.)

* **Equivariance**: a function `f : X → Y` between nominal sets is
  equivariant when it commutes with the action, `f (π • x) = π • f x`.
  Equivariant functions are the natural morphisms of nominal sets.
  A relation `R ⊆ X × X` is equivariant when `R x y` implies
  `R (π • x) (π • y)` for every `π`.

Nominal sets are particularly well-suited to representing syntax
with binders: raw terms quotiented by α-equivalence form a nominal
set, capture-avoiding substitution becomes definable through
freshness, and structural induction extends to *nominal induction*
where the binder case may assume the bound name is fresh for any
given piece of data.

## Contents of this module

* `Atom`, `Perm`, `swap` — the primitives: atoms as an abbreviation
  for `ℕ`, permutations as `Equiv.Perm Atom`, transpositions.
* `IsNominal X` — the typeclass for nominal sets, extending
  `MulAction Perm X`.
* Ground instances of `IsNominal`: `Atom`, `Prop` (trivial action),
  products, function spaces, and `Finset Atom`.
* `Supports`, `FinitelySupported`, `fresh` — the support and
  freshness predicates.
* `exists_notMem`, `exists_fresh`, `exists_fresh₂` — the
  Choose-a-Fresh-Name Principle in three variants.
* `supp` — a finite support for a finitely-supported element,
  extracted classically from the witness.
* `Equivariant`, `Equivariant₂`, `EquivariantRel` — equivariance for
  functions and relations.

## References

* Andrew M. Pitts. *Nominal Sets: Names and Symmetry in Computer
  Science.* Cambridge University Press, 2013.
* Murdoch J. Gabbay, Andrew M. Pitts. *A new approach to abstract
  syntax with variable binding.* Formal Aspects of Computing 13
  (2002), 341–363.
-/
@[expose] public section

namespace LeanTra.Nominal



/-! ### Atoms and permutations

The primitives of the theory. `Atom` is the countably infinite set of
names; `Perm` is the group of bijections of atoms; `swap` is the
transposition of two named atoms. All three are `abbrev`s over
Mathlib types so that decidable equality, group operations,
transpositions, and the `MulAction` on `Equiv.Perm` are inherited
transparently. -/

/-- The countably infinite set `V` of atoms — the primitive names
over which nominal reasoning is parameterised. Realised concretely as
`ℕ` via `abbrev`, so decidable equality, `Finset.sup`, infiniteness,
and every other operation on `ℕ` are inherited transparently.
Consumers should nonetheless treat `Atom` as opaque; the only
operations guaranteed to be meaningful on atoms are equality testing
and permutation. -/
abbrev Atom : Type := Nat

/-- The symmetric group of bijections of atoms with themselves. The
group structure, the `MulAction` on atoms, and the `swap`
transpositions are all inherited from `Equiv.Perm`.

Standard nominal-set theory (Pitts, *Nominal Sets*, Def. 1.13)
restricts attention to *finitary* permutations — those moving only
finitely many atoms. We use the full symmetric group here for
convenience: Mathlib provides `Equiv.Perm` directly, and every
permutation we ever construct concretely (`swap`, and finite
compositions thereof) is finitary anyway. The finitary permutations
form a subgroup of `Equiv.Perm Atom`, and Pitts's theory transports
along this inclusion. -/
abbrev Perm : Type := Equiv.Perm Atom

/-- The transposition of two atoms. `swap a b` fixes every atom other
than `a` and `b`, and exchanges those two. -/
abbrev swap (a b : Atom) : Perm := Equiv.swap a b



/-! ### The `IsNominal` typeclass

A type is *nominal* when it carries a `Perm`-action. The
finite-support condition — the third ingredient of the informal
definition — is expressed per-element by `FinitelySupported x`
below, rather than baked into the class: every concrete carrier we
build turns out to be finitely supported at every element, but the
two concepts are logically independent and Mathlib's `MulAction`
already gives us the action laws for free. -/

/-- A carrier of the `Perm`-action. In the terminology of Pitts's
*Nominal Sets* (Def. 2.2), a **nominal set** is a `Perm`-set *all of
whose elements are finitely supported*. Our `IsNominal` class packages
only the action — it corresponds to Pitts's "`Perm 𝔸`-set" rather
than "nominal set" in the strict sense.

The finite-support condition is expressed per-element by
`FinitelySupported x` below rather than baked into the class. Every
concrete carrier we construct downstream (`Atom`, `Prop`, products,
function spaces, `Finset Atom`, and the syntactic types `RawLam`,
`Lam`, `Subst`) turns out to be a genuine nominal set in Pitts's
sense — every element is finitely supported — but the two concepts
are logically separable, so we keep them separate at the typeclass
level.

Named `IsNominal` to avoid clashing with the surrounding
namespace. -/
class IsNominal (X : Type*) extends MulAction Perm X



/-! ### Nominal structure on the ground types

`Perm` acts on the ambient mathematical universe (propositions,
products, function spaces, finite sets of atoms) in canonical ways.
These instances allow the general vocabulary — "equivariant
relation on `X`", "finitely-supported map `Atom → X`", etc. — to
apply uniformly, without redefining the action for each new carrier
built from these constructors. -/

/-- Atoms are permuted by applying the permutation itself. -/
instance instMulActionAtom : MulAction Perm Atom where
  smul π a := π a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : IsNominal Atom where

/-- Propositions carry the trivial action: renaming atoms doesn't
change truth values. As a consequence, equivariance for a
`Prop`-valued predicate becomes a separate, non-trivial condition
imposed at the use site — not automatically satisfied by the action
alone. -/
instance instMulActionProp : MulAction Perm Prop where
  smul _ p := p
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : IsNominal Prop where

/-- Products act componentwise: `π • (x, y) = (π • x, π • y)`. -/
instance instMulActionProd {X Y : Type*} [MulAction Perm X] [MulAction Perm Y] :
    MulAction Perm (X × Y) where
  smul π p := (π • p.1, π • p.2)
  one_smul p := by
    change ((1 : Perm) • p.1, (1 : Perm) • p.2) = p
    rw [one_smul, one_smul]
  mul_smul π₁ π₂ p := by
    change ((π₁ * π₂) • p.1, (π₁ * π₂) • p.2)
       = (π₁ • π₂ • p.1, π₁ • π₂ • p.2)
    rw [mul_smul, mul_smul]

instance {X Y : Type*} [IsNominal X] [IsNominal Y] : IsNominal (X × Y) where

/-- Function-space action: `(π • f) x := π • f (π⁻¹ • x)`. This is
the "conjugation" action, chosen so that `f` is equivariant precisely
when `f` commutes with the atomic permutation
(`f (π • x) = π • f x`), which is equivalent to `π • f = f` under
this action. -/
instance instMulActionForall {X Y : Type*}
    [MulAction Perm X] [MulAction Perm Y] :
    MulAction Perm (X → Y) where
  smul π f := fun x => π • f (π⁻¹ • x)
  one_smul f := by
    funext x
    change (1 : Perm) • f ((1 : Perm)⁻¹ • x) = f x
    rw [inv_one, one_smul, one_smul]
  mul_smul π₁ π₂ f := by
    funext x
    change (π₁ * π₂) • f ((π₁ * π₂)⁻¹ • x)
       = π₁ • ((π₂ • fun y => f (π₂⁻¹ • y)) (π₁⁻¹ • x))
    change (π₁ * π₂) • f ((π₁ * π₂)⁻¹ • x)
       = π₁ • π₂ • f (π₂⁻¹ • π₁⁻¹ • x)
    rw [mul_smul, mul_inv_rev, mul_smul]

instance {X Y : Type*} [IsNominal X] [IsNominal Y] : IsNominal (X → Y) where

/-- Finite sets of atoms are permuted by taking the pointwise image
`π • S = { π a | a ∈ S }`. -/
instance instMulActionFinsetAtom : MulAction Perm (Finset Atom) where
  smul π S := S.image (fun a => π • a)
  one_smul S := by
    change S.image (fun a => (1 : Perm) • a) = S
    have : (fun a : Atom => (1 : Perm) • a) = id := by
      funext a; exact one_smul _ _
    rw [this, Finset.image_id]
  mul_smul π₁ π₂ S := by
    change S.image (fun a => (π₁ * π₂) • a)
       = (S.image (fun a => π₂ • a)).image (fun a => π₁ • a)
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a _
    exact mul_smul π₁ π₂ a

instance : IsNominal (Finset Atom) where



/-! ### Support and freshness

The support of an element `x` is the finite set of atoms that `x`
actually depends on: any permutation shuffling only atoms outside
the support leaves `x` fixed. Three predicates capture this:

* `Supports S x` — `S` is *a* support for `x` (not necessarily the
  smallest).
* `FinitelySupported x` — some finite support exists.
* `fresh a x` (`a # x`) — the atom `a` sits outside some support of
  `x`, i.e. `x` does not depend on `a`. -/

variable {X : Type*} [MulAction Perm X]

/-- `S` supports `x`: every permutation that fixes each atom of `S`
pointwise leaves `x` unchanged. -/
def Supports (S : Finset Atom) (x : X) : Prop :=
  ∀ π : Perm, (∀ a ∈ S, π • a = a) → π • x = x

/-- `x` has finite support: at least one finite set of atoms supports
it. -/
def FinitelySupported (x : X) : Prop :=
  ∃ S : Finset Atom, Supports S x

/-- The atom `a` is **fresh** for `x`, written `a # x`, when `a` lies
outside some support of `x` — equivalently, `x` does not depend on
`a`. -/
def fresh (a : Atom) (x : X) : Prop :=
  ∃ S : Finset Atom, Supports S x ∧ a ∉ S

@[inherit_doc] scoped infix:50 " # " => fresh



/-! ### Basic support lemmas

Elementary consequences of the definitions: support is monotone in
its `Finset` argument (a superset of a support is still a support),
finite support is closed under widening, and the two ground types
`Atom` and `Prop` are finitely supported. -/

/-- Enlarging the candidate support set preserves the support
relation: if `S` supports `x` and `S ⊆ T`, then `T` supports `x`
as well. -/
theorem Supports.mono {S T : Finset Atom} {x : X}
    (hST : S ⊆ T) (hS : Supports S x) : Supports T x :=
  fun π hπ => hS π (fun a haS => hπ a (hST haS))

/-- Exhibiting any finite support witnesses finite supportedness. -/
theorem FinitelySupported.of_supports {S : Finset Atom} {x : X}
    (h : Supports S x) : FinitelySupported x :=
  ⟨S, h⟩

/-- Every atom has finite support: the singleton `{a}` supports `a`
itself. -/
theorem atom_finitelySupported (a : Atom) : FinitelySupported a :=
  ⟨{a}, fun _ hπ => hπ a (Finset.mem_singleton.mpr rfl)⟩

/-- Every proposition is finitely supported by the empty set, since
the `Perm`-action on `Prop` is trivial. -/
theorem prop_finitelySupported (p : Prop) : FinitelySupported p :=
  ⟨∅, fun _ _ => rfl⟩



/-! ### The support function

Pitts (Prop. 2.3, eq. 2.4) defines the **support** `supp x` of a
finitely-supported element as the intersection of all its finite
supports, and shows this is itself the least support. Constructing
the intersection in Lean would require Pitts's Prop. 2.3 (that the
intersection of two finite supports is again a support) followed by
a well-founded argument.

For our downstream needs a weaker version suffices: extract *some*
finite support by classical choice on the `FinitelySupported`
witness. The result is a finite support, but not necessarily the
least. Named `supp` for consistency with Pitts's notation, with the
proviso that minimality is not proved here. -/

/-- A finite support for a finitely-supported element, extracted
classically from the witness. The result is *some* support, not
necessarily the least (which Pitts obtains as the intersection of
all finite supports — a strengthening deferred here). -/
noncomputable def supp {x : X} (hx : FinitelySupported x) : Finset Atom :=
  Classical.choose hx

/-- The set produced by `supp` does support the element. -/
theorem supp_supports {x : X} (hx : FinitelySupported x) :
    Supports (supp hx) x :=
  Classical.choose_spec hx

/-- An atom outside `supp hx` is fresh for `x`. -/
theorem fresh_of_notMem_supp {x : X} (hx : FinitelySupported x) {a : Atom}
    (ha : a ∉ supp hx) : a # x :=
  ⟨supp hx, supp_supports hx, ha⟩



/-! ### The Choose-a-Fresh-Name Principle

The **Choose-a-Fresh-Name Principle** (Pitts, *Nominal Sets*, Ch. 3)
is the fact that gives nominal reasoning its practical strength:
given any finitely-supported element `x` and any finite set of atoms
`A`, there is an atom `a` that is both fresh for `x` and outside
`A`. Combined with equivariance, this permits arguments of the form
*"choose a bound-variable name fresh for everything currently in
play"* — the informal Barendregt convention made mathematically
precise.

The principle rests on a very concrete fact: `V` is countably
infinite, so any finite subset omits an atom.

(Terminology: Pitts also uses the phrase *Finite Support Principle*
for a distinct meta-theorem asserting that objects definable from
finitely-supported data in classical higher-order logic are
themselves finitely supported. That principle is not formalised
here — we invoke individual instances of it as needed.) -/

/-- Any finite set of atoms omits some atom. Since `Atom = ℕ`, we
concretely take `A.sup id + 1`. -/
theorem exists_notMem (A : Finset Atom) : ∃ a : Atom, a ∉ A := by
  refine ⟨A.sup id + 1, ?_⟩
  intro hmem
  have hle : A.sup id + 1 ≤ A.sup id :=
    Finset.le_sup (f := id) hmem
  exact Nat.not_succ_le_self _ hle

/-- **The Finite Support Principle.** For any finitely-supported `x`
and any finite set of atoms `A`, there is an atom outside `A` that
is fresh for `x`. -/
theorem exists_fresh (x : X) (hx : FinitelySupported x) (A : Finset Atom) :
    ∃ a : Atom, a ∉ A ∧ a # x := by
  obtain ⟨S, hS⟩ := hx
  obtain ⟨a, ha⟩ := exists_notMem (A ∪ S)
  refine ⟨a, fun hA => ha (Finset.mem_union.mpr (Or.inl hA)),
          S, hS, fun hS' => ha (Finset.mem_union.mpr (Or.inr hS'))⟩

/-- Two-element variant: an atom fresh for two elements
simultaneously and outside an auxiliary finite set. -/
theorem exists_fresh₂ {Y : Type*} [MulAction Perm Y]
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

A function or relation is **equivariant** when it commutes with the
permutation action — renaming the input and renaming the output are
interchangeable. Equivariant maps are the natural morphisms of
nominal sets, and equivariant relations are the natural notion of
relation "insensitive to names". -/

/-- A function `f : X → Y` is equivariant when `f (π • x) = π • f x`
for every permutation `π` and input `x`. -/
def Equivariant {Y : Type*} [MulAction Perm Y] (f : X → Y) : Prop :=
  ∀ (π : Perm) (x : X), f (π • x) = π • f x

/-- Binary version: `f : X → Y → Z` is equivariant when it commutes
with the action in both arguments simultaneously. -/
def Equivariant₂ {Y Z : Type*} [MulAction Perm Y] [MulAction Perm Z]
    (f : X → Y → Z) : Prop :=
  ∀ (π : Perm) (x : X) (y : Y), f (π • x) (π • y) = π • f x y

/-- A binary relation `R` is equivariant when related pairs stay
related after any renaming. Since the `Perm`-action on `Prop` is
trivial, the biconditional collapses to the forward direction; the
converse is derived in `EquivariantRel.iff`. -/
def EquivariantRel (R : X → X → Prop) : Prop :=
  ∀ (π : Perm) (x y : X), R x y → R (π • x) (π • y)

/-- For equivariant relations the forward-closure is in fact a
biconditional: `R (π • x) (π • y) ↔ R x y`. -/
theorem EquivariantRel.iff {R : X → X → Prop}
    (hR : EquivariantRel R) (π : Perm) (x y : X) :
    R (π • x) (π • y) ↔ R x y := by
  refine ⟨fun h => ?_, hR π x y⟩
  have := hR π⁻¹ _ _ h
  rwa [← mul_smul, inv_mul_cancel, one_smul, ← mul_smul, inv_mul_cancel,
       one_smul] at this

end LeanTra.Nominal
