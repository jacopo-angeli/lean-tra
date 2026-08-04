/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Function.Basic

/-!
# First-order terms in context — syntax and substitution

Phase A of the LICS'26 term-model construction: the pure syntactic layer.
Neither relations nor any `SRA` structure appear here — this file only sets
up terms, substitution, and their monoid equational theory, so that Phase B
(candidate relations on `Tm`) and Phase C (the `SRA` instance) can be built
on top without revisiting the syntax.

## Contents

* `Signature` — a type of operation symbols with an arity function.
* `Tm S Γ` — first-order S-terms with variables drawn from `Γ`.
* `Tm.subst`, `Tm.ren` — capture-free simultaneous substitution and its
  renaming restriction.
* `Subst.id`, `Subst.comp` — the Kleisli identity and composition
  associated to `Tm`.
* Substitution laws: `Tm.subst_var`, `Tm.subst_node`, `Tm.subst_id`,
  `Tm.subst_comp`, `Subst.comp_assoc`, `Subst.id_comp`, `Subst.comp_id`,
  and the mixed `Tm.subst_ren`, `Tm.ren_subst`, `Tm.ren_ren`, `Tm.ren_id`.
* `ClosedTm`, `Tm.close`, `Tm.subst_close` — closed terms and their
  weakening into an arbitrary context.

## Design decisions

### (D1) Contexts as types

The paper (Gavazzo, LICS'26, §3.1.1) takes contexts to be *finite subsets*
of a fixed variable set `V`, and defines a renaming from `Γ` to `Δ` as
*any* map `ρ : Γ → Δ` between the underlying sets — not necessarily an
inclusion. Example 3(2) reinforces this by writing "for any function
(renaming) f : i → j". We promote the context to a type parameter of
`Tm`: `Tm S Γ` are terms whose variables come from `Γ`, renamings are
plain functions `Γ → Δ` (faithful to the paper — not a generalisation),
and substitutions are functions `Γ → Tm S Δ`. Closed terms are
`Tm S Empty`.

*Rationale.* Finiteness of contexts is used nowhere in the sixteen `SRA`
axioms; the paper needs it only to give a meaning to the "finite support"
of a global substitution. What contexts-as-types costs is freshness
bookkeeping — and freshness is exactly what will bite in Phase C, where
associativity of relational substitution has to merge one witness per
variable. With contexts-as-types that merge is a dependent sum over `Γ`;
with finite sets it is a fresh renaming. We accept the dependent-sum cost
in exchange for the disappearance of every capture-avoidance lemma.

### (D2) Indexed family, not the flat union

Gavazzo uses both views of the term algebra — `T_S(Γ)` as a family indexed
by finite contexts, and the flat union `T_S(V) := ⋃_Γ T_S(Γ)` on which
global substitution is defined. We keep the indexed family. The flat view
makes a term of a small context *literally* a term of a larger one, which
is convenient but pushes relations into a *global* composition, and with
global composition the modal law `□(R * S) ≤ □R * □S` fails: the flat
variant is not a model of the `SRA` axioms. The price we pay for keeping
the family is that a term and any of its weakenings are distinct objects
that must be transported by an explicit `Tm.ren`. Phase B relations will
have to be closed under renaming; the mixed subst/ren laws below are
stated with that in mind.

### (D3) Arbitrary signature

`Signature` is data — a type `op` of operation symbols with an arity
function `op → ℕ` — following Def. 8 verbatim. This is deliberately not a
fixed toy signature: matching the paper is the whole point, and it lets a
downstream concrete calculus instantiate the term model directly. For
instance, LICS'26 Example 18 (combinatory logic) takes
`op := {k, s, A}` with `arity k = arity s = 0`, `arity A = 2`.

### Naming note

The paper calls the signature `Σ`; we call it `S`. The character `Σ` is
reserved by Lean 4 for the dependent-sum type former (`Σ x : α, β x`) and
cannot be used as an identifier. Renaming to `S` is the only concession
to Lean syntax made in this file.

## Forward pointers

* `Tm.close` and `Tm.subst_close` are the syntactic content behind the
  closure constant `SRA.j` used in Phase C (the identity on weakened
  closed terms): substitution acts trivially on the image of weakening
  from the empty context, so `j` stays renaming-closed and the derived
  `box := j * · * j` factors through closed terms. (The paper's
  original reading `□a := a[⊥]` survives in Phase C only as the legacy
  facts `substBot_iff` / `substBot_mul` about `subst · ⊥` per se.)
* `Tm.subst_node` is the equation the SRA law `tilde a[b] ≤ (a[b])~` will
  ultimately unfold to at the syntactic level in Phase C.
* `Tm.subst_ren`, `Tm.ren_subst`, `Tm.ren_ren` are exactly the shape
  needed in Phase B, where candidate relations on terms must be verified
  closed under renaming for the `SRA` operations.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. §3.1.1 (Definition 8) is the source for the syntax and
  substitution; Example 3(2) — used mainly in Phase B (relations) — sets
  up the dependent-relation structure that our `SynRel` will refine. The
  reading of substitution as a Kleisli composition of the term monad is
  our own framing, not the paper's; it is convenient because it turns L2,
  L3, L4, L5 into the axioms of a category.
-/
@[expose] public section

namespace LeanTra.Instances.FirstOrder

/-- A first-order signature: a type `op` of operation symbols together
with an arity function `arity : op → ℕ`. Faithful to LICS'26 Def. 8;
kept as unstructured data (no algebraic conditions on `op`) so that any
concrete calculus can supply one directly. -/
structure Signature where
  /-- The type of operation symbols. -/
  op : Type
  /-- Arity of each operation symbol. -/
  arity : op → Nat

/-- First-order `S`-terms whose free variables are drawn from the
"context type" `Γ` (see design decision (D1) in the module docstring):

* `Tm.var x` is the term consisting of the variable `x : Γ`;
* `Tm.node f ts` applies the operation `f` of arity `n = S.arity f` to
  the argument vector `ts : Fin n → Tm S Γ`.

The recursive occurrence sits under the function type `Fin n → _`, which
is strictly positive and accepted by Lean's inductive checker; the
auto-generated recursor `Tm.rec` supplies the expected pointwise induction
hypothesis `∀ i, motive (ts i)` in the `node` case, so the `induction`
tactic just works — no custom eliminator is needed. -/
inductive Tm (S : Signature) (Γ : Type) where
  /-- A variable term. -/
  | var  : Γ → Tm S Γ
  /-- An operation `f` applied to its argument vector `ts`. -/
  | node : (f : S.op) → (Fin (S.arity f) → Tm S Γ) → Tm S Γ

namespace Tm

variable {S : Signature} {Γ Δ E : Type}

/-- Simultaneous capture-free substitution: `t.subst τ` replaces every
occurrence of a variable `x : Γ` in `t` by `τ x : Tm S Δ`. Since contexts
are types and variables have no binding structure at this level (D1),
there is no capture to avoid — substitution is a plain fold. -/
def subst : Tm S Γ → (Γ → Tm S Δ) → Tm S Δ
  | var x,     τ => τ x
  | node f ts, τ => node f (fun i => (ts i).subst τ)

/-- Renaming: the special case of `subst` where the target of each
variable is itself a variable. Kept as a `def` (not an abbreviation) so
that renamings and general substitutions do not confuse the `simp` set,
even though `Tm.ren f = Tm.subst (Tm.var ∘ f)` holds by definition. -/
def ren (t : Tm S Γ) (f : Γ → Δ) : Tm S Δ := t.subst (Tm.var ∘ f)

end Tm

namespace Subst

variable {S : Signature} {Γ Δ E : Type}

/-- The identity substitution `Γ → Tm S Γ`, sending each variable to
itself. Equal to `Tm.var` by definition; the alias records the intended
reading as the identity of the Kleisli category of `Tm`. -/
def id : Γ → Tm S Γ := Tm.var

/-- Kleisli composition of substitutions: `Subst.comp τ θ` applies `τ`
first, then `θ`. Note the argument order — it matches diagrammatic
composition (`τ` first, on the left of the arguments), and is kept
consistent throughout this file. -/
def comp (τ : Γ → Tm S Δ) (θ : Δ → Tm S E) : Γ → Tm S E :=
  fun x => (τ x).subst θ

end Subst

namespace Tm

variable {S : Signature} {Γ Δ E Z : Type}

/-! ## L1, L7 — reduction laws for `subst` on the two constructors. -/

/-- L1: substitution on a variable term is application of the
substitution. Definitionally true; recorded as a named `simp` lemma. -/
@[simp]
theorem subst_var (x : Γ) (τ : Γ → Tm S Δ) : (var x).subst τ = τ x := rfl

/-- L7: substitution commutes with the `node` constructor.
Definitionally true; recorded as a named `simp` lemma because Phase C
will cite it as the syntactic content behind the SRA law
`tilde a[b] ≤ (a[b])~`. -/
@[simp]
theorem subst_node (f : S.op) (ts : Fin (S.arity f) → Tm S Γ)
    (τ : Γ → Tm S Δ) :
    (node f ts).subst τ = node f (fun i => (ts i).subst τ) := rfl

/-! ## L2, L3 — the two structural inductions.

Everything below is a corollary of these two. -/

/-- `ren` on a variable is application. Definitionally true; the named
`simp` lemma is what Phase C uses to peel `ren_closed` obligations for
relations built out of `Tm.var`. -/
@[simp]
theorem ren_var (x : Γ) (f : Γ → Δ) :
    (var x : Tm S Γ).ren f = var (f x) := rfl

/-- `ren` commutes with the `node` constructor. Definitionally true;
the named `simp` lemma is what Phase C uses to peel `ren_closed`
obligations for relations built out of `Tm.node`. -/
@[simp]
theorem ren_node (g : S.op) (ts : Fin (S.arity g) → Tm S Γ) (f : Γ → Δ) :
    (node g ts).ren f = node g (fun i => (ts i).ren f) := rfl

/-- L2: the identity substitution is a right identity for `subst`. Proved
by induction on the term; the `node` case needs `funext` to transport
the pointwise IH into equality of the argument vectors. -/
theorem subst_id (t : Tm S Γ) : t.subst Subst.id = t := by
  induction t with
  | var x => rfl
  | node f ts ih =>
    change node f (fun i => (ts i).subst Subst.id) = node f ts
    apply congrArg (node f)
    funext i
    exact ih i

/-- L3: substitution respects Kleisli composition —
`(t.subst τ).subst θ = t.subst (τ ; θ)`. Proved by induction on the
term. -/
theorem subst_comp (t : Tm S Γ) (τ : Γ → Tm S Δ) (θ : Δ → Tm S E) :
    (t.subst τ).subst θ = t.subst (Subst.comp τ θ) := by
  induction t with
  | var x => rfl
  | node f ts ih =>
    change node f (fun i => ((ts i).subst τ).subst θ)
        = node f (fun i => (ts i).subst (Subst.comp τ θ))
    apply congrArg (node f)
    funext i
    exact ih i

/-! ## L6 and the mixed subst/ren laws.

The four laws below are all corollaries of `subst_comp` and `subst_id`.
We keep them named because Phase B has to check, for every candidate
relation on `Tm`, that it is closed under renaming for each `SRA`
operation, and each of the four shapes arises exactly once in that
argument:

* `subst_ren` — a substitution absorbs an inner renaming: needed when
  pushing a substitution through a renamed subterm.
* `ren_subst` — an outer renaming absorbs into the substitution as a
  post-composed renaming per variable: the dual shape.
* `ren_ren` — two renamings compose as expected: the special case of
  `subst_comp` that Phase B needs when transporting a relation along a
  chain of weakenings.
* `ren_id` — the identity renaming is the identity: needed for the
  `varDiag` axiom (`Δη`), which is a reflexive-on-variables relation. -/

/-- Substitution after a renaming: `t.ren f .subst τ = t.subst (τ ∘ f)`. -/
theorem subst_ren (t : Tm S Γ) (f : Γ → Δ) (τ : Δ → Tm S E) :
    (t.ren f).subst τ = t.subst (τ ∘ f) := by
  unfold ren
  rw [subst_comp]
  rfl

/-- Renaming after a substitution: an outer renaming distributes into the
substitution as a post-composed renaming, `t.subst τ .ren g =
t.subst (fun x => (τ x).ren g)`. -/
theorem ren_subst (t : Tm S Γ) (τ : Γ → Tm S Δ) (g : Δ → E) :
    (t.subst τ).ren g = t.subst (fun x => (τ x).ren g) := by
  unfold ren
  rw [subst_comp]
  rfl

/-- L6: composition of renamings. -/
theorem ren_ren (t : Tm S Γ) (f : Γ → Δ) (g : Δ → E) :
    (t.ren f).ren g = t.ren (g ∘ f) := by
  unfold ren
  rw [subst_comp]
  rfl

/-- The identity renaming is the identity. -/
theorem ren_id (t : Tm S Γ) : t.ren _root_.id = t := by
  unfold ren
  change t.subst (fun x => Tm.var x) = t
  exact subst_id t

/-- On an empty context, substitution is invariant in its substitution
argument: `t : Tm S Γ` with `Γ` uninhabited has no `var` leaves, so the
substitution is never consulted. Needed in Phase C for the
`substBot_iff` normal-form lemma. -/
theorem subst_empty [IsEmpty Γ] (t : Tm S Γ) (τ₁ τ₂ : Γ → Tm S Δ) :
    t.subst τ₁ = t.subst τ₂ := by
  induction t with
  | var x => exact isEmptyElim x
  | node g ts ih =>
    change node g (fun i => (ts i).subst τ₁)
         = node g (fun i => (ts i).subst τ₂)
    apply congrArg (node g)
    funext i
    exact ih i

/-- Injectivity of renaming: `Tm.ren f` is injective whenever `f` is.
The `Empty → Δ` case, applied through `Tm.close`, is what identifies
the two empty-context decompositions in the `box_mul` proof. -/
theorem ren_injective (f : Γ → Δ) (hf : Function.Injective f) :
    Function.Injective (fun t : Tm S Γ => t.ren f) := by
  intro t
  induction t with
  | var x =>
    intro s h
    cases s with
    | var y =>
      simp only [ren_var] at h
      exact congrArg Tm.var (hf (Tm.var.inj h))
    | node g ss =>
      simp only [ren_var, ren_node] at h
      cases h
  | node g ts ih =>
    intro s h
    cases s with
    | var y =>
      simp only [ren_var, ren_node] at h
      cases h
    | node g' ss =>
      simp only [ren_node] at h
      injection h with hg hts
      subst hg
      have hts' : (fun i => (ts i).ren f) = (fun i => (ss i).ren f) :=
        eq_of_heq hts
      apply congrArg (node g)
      funext i
      exact ih i (congrFun hts' i)

end Tm

namespace Subst

variable {S : Signature} {Γ Δ E Z : Type}

/-! ## L4, L5 — `Subst.comp` is a monoid on hom-types.

`Subst.id` and `Subst.comp` form a category (with objects the types Γ,
morphisms Γ → Tm S Δ), and these three laws witness its axioms. -/

/-- L4: associativity of Kleisli composition. -/
theorem comp_assoc (τ : Γ → Tm S Δ) (θ : Δ → Tm S E) (κ : E → Tm S Z) :
    comp (comp τ θ) κ = comp τ (comp θ κ) := by
  funext x
  change ((τ x).subst θ).subst κ = (τ x).subst (comp θ κ)
  exact Tm.subst_comp (τ x) θ κ

/-- L5a: `Subst.id` is a left unit for `Subst.comp`. -/
theorem id_comp (τ : Γ → Tm S Δ) : comp Subst.id τ = τ := by
  funext x
  rfl

/-- L5b: `Subst.id` is a right unit for `Subst.comp`. -/
theorem comp_id (τ : Γ → Tm S Δ) : comp τ Subst.id = τ := by
  funext x
  change (τ x).subst Subst.id = τ x
  exact Tm.subst_id (τ x)

end Subst

/-! ## Closed terms and the closure constant's syntactic content.

`ClosedTm S = Tm S Empty`: terms with no free variables. Every closed
term embeds into an arbitrary context by the unique function `Empty → Γ`;
substitution then acts trivially on the image of this embedding, which is
the syntactic fact that will let the closure constant `SRA.j` in Phase C
be interpreted as the identity on weakened closed terms (so that the
derived `box := j * · * j` factors through closed terms). -/

/-- Closed `S`-terms — the empty-context fibre of `Tm`. -/
abbrev ClosedTm (S : Signature) := Tm S Empty

namespace Tm

variable {S : Signature} {Γ Δ : Type}

/-- Weakening of a closed term into an arbitrary context, via the unique
function `Empty → Γ`. The target context `Γ` is explicit because it is
not determined by the closed-term argument, and leaving it implicit
forces every downstream lemma to disambiguate `close t` by ascription. -/
def close (Γ : Type) (t : ClosedTm S) : Tm S Γ := t.ren Empty.elim

/-- Substitution acts trivially on a weakened closed term: the closed
content is preserved and only the target context changes. This is the
syntactic content of the □-modality's absorption law (`□a[b] = □a`) that
Phase C will lift to the relational level. -/
theorem subst_close (Γ Δ : Type) (t : ClosedTm S) (τ : Γ → Tm S Δ) :
    (close Γ t).subst τ = close Δ t := by
  unfold close ren
  rw [subst_comp]
  apply congrArg t.subst
  funext e
  exact e.elim

/-- Renaming acts trivially on a weakened closed term. Special case of
`subst_close` at `τ := Tm.var ∘ f`; recorded separately because Phase B
needs it directly to establish that the □ modality yields a
renaming-closed relation. -/
theorem ren_close (Γ Δ : Type) (t : ClosedTm S) (f : Γ → Δ) :
    (close Γ t).ren f = close Δ t := by
  unfold ren
  exact subst_close Γ Δ t (Tm.var ∘ f)

end Tm

end LeanTra.Instances.FirstOrder
