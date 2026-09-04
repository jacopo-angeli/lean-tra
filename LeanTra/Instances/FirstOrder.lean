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
public import LeanTra.Metatheory.Confluence.Orthogonal

/-!
# The first-order term model of the SRA framework

The first-order term model is the concrete non-trivial companion to the
consistency model of `Instances/Consistency.lean` and to the λ-calculus
instance of `Instances/SecondOrder.lean`. We take an arbitrary
first-order signature `S`, build its term algebra `Tm S Γ` in an arbitrary
type-valued context `Γ`, install on top of it the involutive-quantale
layer of `SynRel S`, discharge the sixteen `SRA` axioms and the four `j`
axioms on the resulting carrier, and read off confluence of orthogonal
parallel reduction as an immediate corollary of the abstract bridge
theorem. The signature is left as a parameter, so any concrete
first-order calculus (combinatory logic, arithmetic, and so on)
instantiates the model directly.

The file is organised in five sections. Section 1 fixes the syntax:
signature, terms in context, substitution and renaming, and their
equational theory as a Kleisli category. Section 2 installs the relational
carrier `SynRel S` together with the full involutive-quantale structure
(lattice, monoid, quantale, involution) built pointwise per context.
Section 3 defines the four `SRA` operations (`varDiag`, `scr`, `subst`,
`j`) and discharges the nineteen accompanying axioms, grouped by
ascending difficulty. Section 4 assembles the SRA typeclass instance,
exhibits two non-degeneracy witnesses certifying that `scr` and `box` are
not identically `⊥` on the term model, and records the model-side
verification of `SRA.IsClosed (subst a j)`. Section 5 reads off confluence
of orthogonal parallel reduction as a direct instantiation of the
abstract bridge theorem, closing the loop with the confluence chapter.

The main design decision, visible on every page, is that contexts are
*types* rather than finite subsets of a global variable universe (see the
Section 1 intro for the argument). This choice makes α-issues disappear
at the syntax level and turns the substitution-associativity merge of
Section 3 into a dependent-sum construction, at the cost of promoting
every context to a genuinely different type.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.FirstOrder

/-! ## Section 1: Signature and first-order terms

The first task is to fix the syntax. `Signature` bundles a type `op` of
operation symbols together with an arity function `op → ℕ`; leaving it
as unstructured data lets any concrete calculus supply its own signature
directly. On top of it, `Tm S Γ` is the type of `S`-terms whose free
variables come from the "context type" `Γ`. Two constructors:
`Tm.var x` wraps a variable, `Tm.node f ts` applies an operation `f` of
arity `n = S.arity f` to an argument vector `ts : Fin n → Tm S Γ`.

The main design decision is that contexts are *types*, not finite
subsets of a global variable universe. Under this reading, renamings
`Γ → Δ` and substitutions `Γ → Tm S Δ` are plain functions, and closed
terms are `Tm S Empty`. Finiteness of contexts is not used anywhere in
the SRA axioms; it would be needed only to give a meaning to the
"finite support" of a global substitution, and no theorem below relies
on that. Contexts-as-types costs us the disappearance of every
α-renaming lemma at the syntactic level, and it buys the entire
substitution-associativity merge for free via dependent sums (see the
Section 3 intro). The price is that a term and any of its weakenings
are distinct objects that must be transported by an explicit `Tm.ren`.

Substitution and renaming are defined by direct recursion. The whole
equational theory of substitution is a handful of one-step inductions
on the term, presented here through a Kleisli-composition reading of
substitution: the auxiliary namespace `Subst` provides `Subst.id` and
`Subst.comp`, and the identity and associativity of `subst` read
directly as the identity and associativity laws of a category. Closed
terms and their weakening close the section: `Tm.close` embeds a closed
term into an arbitrary context via the unique `Empty → Γ`, and
`Tm.subst_close` records that substitution acts trivially on the image
of that embedding. This last fact is the syntactic content behind the
closure constant `j` of Section 3. -/

/-- A first-order signature: a type `op` of operation symbols together
with an arity function `arity : op → ℕ`. Kept as unstructured data (no
algebraic conditions on `op`) so that any concrete calculus can supply
one directly. The symbol `Σ` is reserved by Lean 4 for the
dependent-sum type former, so we use `S` instead. -/
structure Signature where
  /-- The type of operation symbols. -/
  op : Type
  /-- Arity of each operation symbol. -/
  arity : op → Nat

/-- First-order `S`-terms whose free variables are drawn from the
"context type" `Γ`:

* `Tm.var x` is the term consisting of the variable `x : Γ`;
* `Tm.node f ts` applies the operation `f` of arity `n = S.arity f` to
  the argument vector `ts : Fin n → Tm S Γ`.

The recursive occurrence sits under the function type `Fin n → _`, which
is strictly positive and accepted by Lean's inductive checker; the
auto-generated recursor `Tm.rec` supplies the expected pointwise induction
hypothesis `∀ i, motive (ts i)` in the `node` case, so the `induction`
tactic just works. -/
inductive Tm (S : Signature) (Γ : Type) where
  /-- A variable term. -/
  | var  : Γ → Tm S Γ
  /-- An operation `f` applied to its argument vector `ts`. -/
  | node : (f : S.op) → (Fin (S.arity f) → Tm S Γ) → Tm S Γ

namespace Tm

variable {S : Signature} {Γ Δ E : Type}

/-- Simultaneous capture-free substitution: `t.subst τ` replaces every
occurrence of a variable `x : Γ` in `t` by `τ x : Tm S Δ`. Since contexts
are types and variables have no binding structure at this level, there is
no capture to avoid: substitution is a plain fold. -/
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
first, then `θ`. The argument order matches diagrammatic composition (`τ`
first, on the left of the arguments), and is kept consistent throughout
the file. -/
def comp (τ : Γ → Tm S Δ) (θ : Δ → Tm S E) : Γ → Tm S E :=
  fun x => (τ x).subst θ

end Subst

namespace Tm

variable {S : Signature} {Γ Δ E Z : Type}

/-! ### Reduction laws for `subst` on the two constructors

The two named `simp` lemmas below simply restate the defining equations
of `subst` as theorems, one per constructor. Their proof is `rfl`; their
purpose is to be picked up by `simp` as automatic rewrite rules, so that
downstream proofs can canonicalise expressions like `(node f ts).subst τ`
without having to unfold the definition of `subst` by hand. -/

/-- Substitution on a variable term is application of the
substitution. -/
@[simp]
theorem subst_var (x : Γ) (τ : Γ → Tm S Δ) : (var x).subst τ = τ x := rfl

/-- Substitution commutes with the `node` constructor. -/
@[simp]
theorem subst_node (f : S.op) (ts : Fin (S.arity f) → Tm S Γ)
    (τ : Γ → Tm S Δ) :
    (node f ts).subst τ = node f (fun i => (ts i).subst τ) := rfl

/-! ### The two structural inductions

The two laws that turn `subst` from a raw recursive definition into the
Kleisli extension of `Tm.var`: `subst_id` says the identity substitution
is a right identity for `subst`, and `subst_comp` says substitution
respects Kleisli composition (`(t.subst τ).subst θ = t.subst (τ ; θ)`).
Everything below in the section is a corollary of these two, so they are
the technical heart of the equational theory. The two structural-induction
lemmas for `ren` are recorded as `@[simp]` alongside for the same reason
as the two above: to feed the automation. -/

/-- `ren` on a variable is application. -/
@[simp]
theorem ren_var (x : Γ) (f : Γ → Δ) :
    (var x : Tm S Γ).ren f = var (f x) := rfl

/-- `ren` commutes with the `node` constructor. -/
@[simp]
theorem ren_node (g : S.op) (ts : Fin (S.arity g) → Tm S Γ) (f : Γ → Δ) :
    (node g ts).ren f = node g (fun i => (ts i).ren f) := rfl

/-- The identity substitution is a right identity for `subst`. Proved
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

/-- Substitution respects Kleisli composition,
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

/-! ### Composition of renamings and the mixed subst/ren laws

The four laws below are all corollaries of `subst_comp` and `subst_id`.
We keep them named because Section 2 has to check, for every candidate
`SRA` operation, that the resulting `SynRel` is closed under renaming,
and each of the four shapes arises exactly once in that argument:
`subst_ren` when pushing a substitution through a renamed subterm,
`ren_subst` for the dual shape, `ren_ren` for a chain of two weakenings,
and `ren_id` for the identity renaming needed by `varDiag`
(reflexive-on-variables). Two extra facts about renaming, `subst_empty`
and `ren_injective`, close the block: the first says substitution is
invariant on the uninhabited context (needed later by the `subst · ⊥`
normal-form lemma), the second says `ren` is injective whenever the
underlying function is (needed by the `substBot_mul` equality in Section
3). -/

/-- Substitution after a renaming: `(t.ren f).subst τ = t.subst (τ ∘ f)`. -/
theorem subst_ren (t : Tm S Γ) (f : Γ → Δ) (τ : Δ → Tm S E) :
    (t.ren f).subst τ = t.subst (τ ∘ f) := by
  unfold ren
  rw [subst_comp]
  rfl

/-- Renaming after a substitution: an outer renaming distributes into the
substitution as a post-composed renaming,
`(t.subst τ).ren g = t.subst (fun x => (τ x).ren g)`. -/
theorem ren_subst (t : Tm S Γ) (τ : Γ → Tm S Δ) (g : Δ → E) :
    (t.subst τ).ren g = t.subst (fun x => (τ x).ren g) := by
  unfold ren
  rw [subst_comp]
  rfl

/-- Composition of renamings. -/
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
substitution is never consulted. Needed in Section 3 for the
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
the two empty-context decompositions in the `substBot_mul` proof. -/
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

/-! ### `Subst.comp` is a monoid on hom-types

`Subst.id` and `Subst.comp` form a category (objects the types Γ,
morphisms Γ → Tm S Δ), and these three laws witness its axioms:
associativity of Kleisli composition, and the two unit laws. Each is a
direct corollary of the two structural inductions above. -/

/-- Associativity of Kleisli composition. -/
theorem comp_assoc (τ : Γ → Tm S Δ) (θ : Δ → Tm S E) (κ : E → Tm S Z) :
    comp (comp τ θ) κ = comp τ (comp θ κ) := by
  funext x
  change ((τ x).subst θ).subst κ = (τ x).subst (comp θ κ)
  exact Tm.subst_comp (τ x) θ κ

/-- `Subst.id` is a left unit for `Subst.comp`. -/
theorem id_comp (τ : Γ → Tm S Δ) : comp Subst.id τ = τ := by
  funext x
  rfl

/-- `Subst.id` is a right unit for `Subst.comp`. -/
theorem comp_id (τ : Γ → Tm S Δ) : comp τ Subst.id = τ := by
  funext x
  change (τ x).subst Subst.id = τ x
  exact Tm.subst_id (τ x)

end Subst

/-! ### Closed terms and their weakening

`ClosedTm S = Tm S Empty`: terms with no free variables. Every closed
term embeds into an arbitrary context by the unique function `Empty → Γ`,
and substitution then acts trivially on the image of this embedding. This
is the syntactic fact that will let the closure constant `SRA.j` in
Section 3 be interpreted as the identity on weakened closed terms, so
that the derived `box := j * · * j` factors through closed terms. -/

/-- Closed `S`-terms: the empty-context fibre of `Tm`. -/
abbrev ClosedTm (S : Signature) := Tm S Empty

namespace Tm

variable {S : Signature} {Γ Δ : Type}

/-- Weakening of a closed term into an arbitrary context, via the unique
function `Empty → Γ`. The target context `Γ` is explicit because it is
not determined by the closed-term argument, and leaving it implicit would
force every downstream lemma to disambiguate `close t` by ascription. -/
def close (Γ : Type) (t : ClosedTm S) : Tm S Γ := t.ren Empty.elim

/-- Substitution acts trivially on a weakened closed term: the closed
content is preserved and only the target context changes. This is the
syntactic content of the □-modality's absorption law (`□a[b] = □a`) that
Section 3 will lift to the relational level. -/
theorem subst_close (Γ Δ : Type) (t : ClosedTm S) (τ : Γ → Tm S Δ) :
    (close Γ t).subst τ = close Δ t := by
  unfold close ren
  rw [subst_comp]
  apply congrArg t.subst
  funext e
  exact e.elim

/-- Renaming acts trivially on a weakened closed term. Special case of
`subst_close` at `τ := Tm.var ∘ f`; recorded separately because Section
2 needs it directly to establish that the □ modality yields a
renaming-closed relation. -/
theorem ren_close (Γ Δ : Type) (t : ClosedTm S) (f : Γ → Δ) :
    (close Γ t).ren f = close Δ t := by
  unfold ren
  exact subst_close Γ Δ t (Tm.var ∘ f)

end Tm

/-! ## Section 2: Renaming-closed context-indexed relations

With the syntax fixed we build the relational carrier of the term
relation algebra. A `SynRel S` is a family of binary relations on
`Tm S Γ`, one per context type `Γ`, uniformly closed under renaming:
for every `f : Γ → Δ`, transporting both endpoints along `f` preserves
the relation. The clause applies `f` to both endpoints explicitly,
which is the form that makes sense under the contexts-as-types
presentation of Section 1: a naive clause that only asked for the same
pair to remain related would degenerate, because two terms in
different context types are literally different objects and there is
nothing to transport unless we say so.

On this carrier we install the full involutive-quantale structure
required by the SRA framework. The lattice part is inherited pointwise
from the Boolean algebra of `Prop`: `⊤` and `⊥` are the always-true and
always-false relations, binary and set-indexed joins and meets come from
`∨`, `∧`, `∃`, `∀`. Each construction preserves renaming closure for the
same reason: `ren` is applied to both endpoints symmetrically, so the
underlying logical connectives commute with it. Composition is the
per-context relational composition (the intermediate term must live in
the same context as the endpoints, a restriction essentially forced by
typing), the unit is term equality, the quantale distributivity is a
swap of existentials, and the involution is endpoint-swap. A sanity
witness `bot_ne_top` at the end certifies that the carrier does not
collapse to a single point as soon as some type is inhabited. -/

/-- A *syntax relation* on `S`-terms: a family of binary relations on
`Tm S Γ`, one per context type `Γ`, closed under renaming by transport
of both endpoints along any function `f : Γ → Δ`.

Note `SynRel S : Type 1` because `rel` quantifies over `Γ : Type`. All
the Mathlib typeclasses used here are `Type u`-polymorphic, so
instantiating them at `Type 1` is unproblematic. -/
structure SynRel (S : Signature) : Type 1 where
  /-- The underlying context-indexed family of relations. -/
  rel : (Γ : Type) → Tm S Γ → Tm S Γ → Prop
  /-- Uniform renaming closure: transporting both endpoints along any
  `f : Γ → Δ` preserves the relation. -/
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

/-! ### Order and pointwise lattice operations

The order on `SynRel` is pointwise implication of the underlying
relations, and every lattice operation is inherited pointwise from
`Prop`. Each of the instances below constructs a `SynRel` via named-field
syntax `{ rel := …, ren_closed := … }` rather than the anonymous
constructor: the anonymous form triggers Lean's implicit-lambda
insertion at the `ren_closed` field, whose type has alternating
explicit/implicit binders, and mis-binds the proof argument to an
implicit position. Named-field syntax sidesteps the issue entirely. -/

/-- The order on `SynRel`: pointwise implication of the underlying
relations. -/
instance instLE : LE (SynRel S) :=
  ⟨fun φ ψ => ∀ Γ (t s : Tm S Γ), φ.rel Γ t s → ψ.rel Γ t s⟩

/-- Unfolding of `≤` as pointwise implication. -/
theorem le_iff {φ ψ : SynRel S} :
    φ ≤ ψ ↔ ∀ Γ (t s : Tm S Γ), φ.rel Γ t s → ψ.rel Γ t s :=
  Iff.rfl

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

/-- Pointwise arbitrary join. -/
instance instSupSet : SupSet (SynRel S) := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∃ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h
    obtain ⟨φ, hφ𝒮, h⟩ := h
    exact ⟨φ, hφ𝒮, φ.ren_closed f h⟩
}⟩

/-- Pointwise arbitrary meet. -/
instance instInfSet : InfSet (SynRel S) := ⟨fun 𝒮 => {
  rel := fun Γ t s => ∀ φ ∈ 𝒮, φ.rel Γ t s
  ren_closed := by
    intros _ _ f _ _ h φ hφ𝒮
    exact φ.ren_closed f (h φ hφ𝒮)
}⟩

/-! ### `.rel` accessors: the pointwise semantics of each operation

The eight `@[simp]` lemmas below expose the underlying `∀`/`∃`/`∧`/`∨`
structure of every lattice operation to Lean's rewrite tactic, so that
downstream proofs can canonicalise `(φ ⊔ ψ).rel Γ t s` into
`φ.rel Γ t s ∨ ψ.rel Γ t s` without unfolding the `SynRel`
constructors. The last two (`iSup_rel`, `biSup_rel`) rewrite the notation
`⨆ i, f i` and `⨆ a ∈ s, f a` into the same pointwise `∃` form; they
are needed by the quantale distributivity proofs. -/

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

/-! ### Complete lattice

The `CompleteLattice` instance packages the pointwise operations above
into the Mathlib typeclass the abstract framework consumes. It is built
manually rather than via `Mathlib.completeLatticeOfInf` so that the
pointwise semantics of `sSup`, `sInf`, `⊔`, `⊓`, `⊤`, `⊥` is preserved
definitionally: a closure-operator-style `sSup` would break the
definitional shape and force us to prove `sSup` equals the pointwise
`∃` before every quantale use. -/

/-- The complete lattice structure on `SynRel S`. -/
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

/-! ### Composition, identity, quantale, involution

Above the lattice we install the multiplicative and involutive structure
that turns `SynRel S` into an involutive quantale. Multiplication is
per-context relational composition (the intermediate term is quantified
in the same context as the endpoints, a restriction essentially forced
by typing under contexts-as-types), the unit is term equality, the
quantale law is a swap of existentials under the pointwise `sSup`, and
the involution is endpoint-swap. All proofs are one-step manipulations
of the underlying `∃`/`∧` structure. -/

/-- Composition of relations, per context: the intermediate term is
quantified in the same context as the endpoints. -/
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

/-- Composition distributes over arbitrary joins on both sides, the two
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
  converse_involutivity _ := by ext; rfl
  converse_compositionality φ ψ := by
    ext Γ t v
    constructor
    · rintro ⟨u, hφ, hψ⟩; exact ⟨u, hψ, hφ⟩
    · rintro ⟨u, hψ, hφ⟩; exact ⟨u, hφ, hψ⟩
  converse_monotonicity h Γ t s h' := h Γ s t h'

/-! ### Sanity checks

Non-degeneracy of the carrier: as soon as some type is inhabited (we use
`Unit`), `⊥` and `⊤` are witnessed by concretely different pairs. This
is the analogue of `bot_ne_top` in `Instances/Consistency.lean`, but on
a genuinely non-collapsed carrier. -/

/-- The carrier is non-degenerate: `⊥ ≠ ⊤`. Witnessed at
`Γ := Unit`, `t = s = Tm.var ()`, where `⊤` is `True` and `⊥` is
`False`. Contrast with `Instances/Consistency.lean`, where `⊤ ≠ ⊥`
also holds but every proper relation is forced to collapse. -/
theorem bot_ne_top : (⊥ : SynRel S) ≠ ⊤ := by
  intro h
  have hle : (⊤ : SynRel S) ≤ ⊥ := h ▸ le_refl _
  exact hle Unit (Tm.var ()) (Tm.var ()) trivial

/-- The carrier is `Nontrivial`. Corollary of `bot_ne_top`. -/
instance instNontrivial : Nontrivial (SynRel S) :=
  ⟨⊥, ⊤, bot_ne_top⟩

/-! ## Section 3: SRA operations and their axioms

The heart of the file. On the involutive quantale `SynRel S` we define
the four SRA-specific data and discharge the nineteen accompanying
axioms. The variable co-equivalence `varDiag` is the diagonal restricted
to variables (the pair `(Tm.var x, Tm.var x)` for each `x : Γ`). The
strict compatible refinement `scr φ` propagates `φ` through the term
constructor, relating `node g ts` to `node g ss` whenever the argument
vectors are pointwise `φ`-related. Relation substitution `subst φ ψ`
(written `φ[ψ]` in informal notation) relates two terms `u v : Tm S Θ`
when there exist a source context `Γ`, pre-substitution terms
`t s : Tm S Γ`, and substitutions `τ σ : Γ → Tm S Θ` such that
`u = t.subst τ`, `v = s.subst σ`, `t` and `s` are `φ`-related in `Γ`,
and `τ x` and `σ x` are pointwise `ψ`-related in `Θ`. The closure
constant `j` is the identity restricted to weakened closed terms, and
the derived modality `box := j * · * j` factors through closed terms.

Two design details of `subst` are worth flagging. First, the
pre-substitution terms `t` and `s` live in the source context `Γ` and
not in the target `Θ`: substitution takes a `Γ`-term to a `Θ`-term, so
the outer `∃` binds `Γ`, `t`, `s`, `τ`, `σ` all together as a single
decomposition witness. Second, the equation `u = t.subst τ` has many
solutions in `(t, τ)`, so `t` and `τ` are not determined by `u` alone:
the definition quantifies existentially over the whole decomposition,
with explicit equalities `u = t.subst τ` and `v = s.subst σ` in the
body of the `∃`. The `∃ (Γ : Type)` inside a `Prop`-valued `rel` is
fine by impredicativity of `Prop`, so `SynRel S` stays at `Type 1`.

The nineteen axioms are proved in three groups by ascending difficulty.
Group 1 collects the easy ones: monotonicity of `scr` and `subst`,
converse-commutations, join preservation of `subst`, and the symmetry
and cotransitivity of `varDiag`, all provable by direct unfolding.
Group 2 is the medium block: the two unit laws for substitution (the
right one is where `SynRel`'s renaming-closure clause earns its keep,
via `Classical.axiomOfChoice`), compositionality of `scr` (also using
choice), the oplaxity of `subst` on `scr`, and the fixed-point law plus
structural induction on term shape. Group 3 has the two hard axioms:
`subst_associativity`, whose (≥) direction merges per-variable
decompositions into a single source context via a dependent sum (the
payoff of contexts-as-types: with finite subsets of a global variable
universe this merge would need a fresh renaming per variable, and every
downstream lemma would carry a freshness side condition), and
`subst_compositionality_oplax`, which is an inequality because the RHS
decomposes independently on each side of the outer composition.

The section ends with the closure constant `j` and its four axioms, and
retains for the record the legacy `substBot_iff` / `substBot_mul`
characterisation of `subst · ⊥`. These two theorems used to discharge
the earlier `box := subst · ⊥` reading; under the current
`box := j * · * j` interpretation they no longer feed the SRA instance,
but they document the earlier presentation and remain useful facts about
`subst · ⊥` per se. -/

/-- The variable co-equivalence `Δη`: two terms are `varDiag`-related
when they are the same variable. Renaming closure is immediate: the
common variable transports to its `f`-image. -/
def varDiag : SynRel S := {
  rel := fun Γ t s => ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩
}

/-- Strict compatible refinement `tilde φ`: two terms are `scr φ`-related
when they are built from the same outermost operator whose immediate
sub-terms are pairwise `φ`-related. Renaming closure passes through
each sub-term via `φ.ren_closed`. -/
def scr (φ : SynRel S) : SynRel S := {
  rel := fun Γ t s =>
    ∃ (g : S.op) (ts ss : Fin (S.arity g) → Tm S Γ),
      t = Tm.node g ts ∧ s = Tm.node g ss ∧ ∀ i, φ.rel Γ (ts i) (ss i)
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨g, ts, ss, ht, hs, hi⟩ := h
    refine ⟨g, fun i => (ts i).ren f, fun i => (ss i).ren f,
            by rw [ht]; rfl, by rw [hs]; rfl, fun i => ?_⟩
    exact φ.ren_closed f (hi i)
}

/-- Relation substitution `subst φ ψ` (`φ[ψ]`): at context `Θ`, two
terms `u v : Tm S Θ` are related when there exist a source context
`Γ`, a decomposition `u = t.subst τ`, `v = s.subst σ` with `t s : Tm S
Γ` and `τ σ : Γ → Tm S Θ`, such that `t` and `s` are `φ`-related in
`Γ` and, variable-by-variable, `τ x` and `σ x` are `ψ`-related in
`Θ`. -/
def subst (φ ψ : SynRel S) : SynRel S := {
  rel := fun Θ u v =>
    ∃ (Γ : Type) (t s : Tm S Γ) (τ σ : Γ → Tm S Θ),
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

/-! ### `.rel` accessors: pointwise semantics of each operation -/

/-- `varDiag` at the level of `.rel`. -/
@[simp] theorem varDiag_rel {Γ} {t s : Tm S Γ} :
    (varDiag : SynRel S).rel Γ t s ↔ ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x :=
  Iff.rfl

/-- `scr` at the level of `.rel`. -/
@[simp] theorem scr_rel {φ : SynRel S} {Γ} {t s : Tm S Γ} :
    (scr φ).rel Γ t s ↔
      ∃ (g : S.op) (ts ss : Fin (S.arity g) → Tm S Γ),
        t = Tm.node g ts ∧ s = Tm.node g ss ∧ ∀ i, φ.rel Γ (ts i) (ss i) :=
  Iff.rfl

/-- `subst` at the level of `.rel`. -/
@[simp] theorem subst_rel {φ ψ : SynRel S} {Θ} {u v : Tm S Θ} :
    (subst φ ψ).rel Θ u v ↔
      ∃ (Γ : Type) (t s : Tm S Γ) (τ σ : Γ → Tm S Θ),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel Γ t s ∧ ∀ x, ψ.rel Θ (τ x) (σ x) :=
  Iff.rfl

/-! ### Group 1: the easy axioms

Six axioms provable by direct unfolding of the definitions, with no
appeal to choice and no threading through the `lam`/`node` case
distinctions. Monotonicity of `scr` and of `subst` in its second
argument, converse-commutation for both, join preservation of `subst` in
the first argument, symmetry and co-transitivity of `varDiag`, and the
orthogonality `varDiag * scr φ ≤ ⊥` (a variable is never simultaneously
a compound term). -/

/-- Monotonicity of `scr`. -/
theorem scr_monotonicity {φ ψ : SynRel S} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro Γ t s hs
  obtain ⟨g, ts, ss, ht, hs', hi⟩ := hs
  exact ⟨g, ts, ss, ht, hs', fun i => h Γ (ts i) (ss i) (hi i)⟩

/-- Monotonicity of `subst` in the second argument. -/
theorem subst_monotonicity_right {φ ψ ψ' : SynRel S} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro Θ u v hs
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨Γ, t, s, τ, σ, hu, hv, hφ, fun x => h Θ (τ x) (σ x) (hψ x)⟩

/-- `scr` commutes with converse. -/
theorem scr_converse_commutation (φ : SynRel S) : scr (φᵒ) = (scr φ)ᵒ := by
  ext Γ t s
  constructor
  · rintro ⟨g, ts, ss, rfl, rfl, hi⟩
    exact ⟨g, ss, ts, rfl, rfl, fun i => hi i⟩
  · rintro ⟨g, ts, ss, rfl, rfl, hi⟩
    exact ⟨g, ss, ts, rfl, rfl, fun i => hi i⟩

/-- Converse commutes with `subst`, swapping both arguments' converses. -/
theorem subst_converse_commutation (φ ψ : SynRel S) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

/-- `subst` preserves arbitrary joins in the first argument. -/
theorem subst_join_preservation_left (𝒮 : Set (SynRel S)) (ψ : SynRel S) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

/-- Symmetry of `varDiag`: swapping endpoints is absorbed. -/
theorem varDiag_symmetry : (varDiag : SynRel S)ᵒ ≤ varDiag := by
  intro Γ t s h
  obtain ⟨x, hs, ht⟩ := h
  exact ⟨x, ht, hs⟩

/-- Co-transitivity of `varDiag`: relating two variables through an
intermediate variable is direct. -/
theorem varDiag_cotransitivity : (varDiag : SynRel S) ≤ varDiag * varDiag := by
  intro Γ t s h
  obtain ⟨x, ht, hs⟩ := h
  exact ⟨Tm.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

/-- Variables and compound terms are disjoint: `Δη ; tilde φ` collapses to
`⊥`. Proof: the `varDiag` intermediate forces `u = Tm.var x`, while the
`scr` intermediate forces `u = Tm.node g ts`, impossible by
`Tm.noConfusion`. -/
theorem varDiag_scr_orthogonality (φ : SynRel S) :
    (varDiag : SynRel S) * scr φ ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨x, _, rfl⟩, ⟨g, ts, ss, hu, _, _⟩⟩ := h
  cases hu

/-! ### Group 2: the medium axioms

Six axioms whose proofs need a bit more machinery. The two unit laws for
`subst` are here: the left one is direct, the right one is where the
renaming-closure clause of `SynRel` earns its keep. In the right-unit
proof, the `varDiag` witnesses in the ψ-slot force `τ x = σ x = Tm.var
(ρ x)` for some `ρ : Γ → Δ`, so the substituted forms become renamings
by `ρ` and the ≤ direction is a direct application of `φ.ren_closed`;
extracting `ρ` from `∀ x, ∃ y, τ x = var y ∧ σ x = var y` needs
`Classical.axiomOfChoice`, the first appeal to choice in the file.
`scr_compositionality` is next, again needing choice to pick a per-argument
middle term from the pointwise composite; then the oplax law
`subst (scr φ) ψ ≤ scr (subst φ ψ)`, which is an inequality because the
right-hand side is strictly more permissive (each argument may carry an
independent decomposition). The section closes with the fixed-point law
`Δη ⊔ scr 1 = 1` and structural induction, the latter proved by a
literal `induction t`. -/

/-- `varDiag` is a left unit for `subst`: the `varDiag`-witness in the
first argument forces `t = s = Tm.var x`, and the substituted forms
become `τ x` and `σ x` which are directly ψ-related. Reverse direction
takes `Γ := Unit`, `t = s := Tm.var ()`. No choice needed. -/
theorem subst_varDiag_unit_left (ψ : SynRel S) : subst varDiag ψ = ψ := by
  ext Θ u v
  constructor
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨Unit, Tm.var (), Tm.var (), fun _ => u, fun _ => v,
            rfl, rfl, ⟨(), rfl, rfl⟩, ?_⟩
    intro _; exact hψ

/-- `varDiag` is a right unit for `subst`. The `varDiag` witnesses in the
ψ-slot pin `τ` and `σ` to renamings `Tm.var ∘ ρ`, so the substituted
forms are `t.ren ρ` and `s.ren ρ`, and the ≤ direction becomes
`φ.ren_closed`. Extracting `ρ` from
`∀ x, ∃ y, τ x = var y ∧ σ x = var y` uses `Classical.axiomOfChoice`. -/
theorem subst_varDiag_unit_right (φ : SynRel S) : subst φ varDiag = φ := by
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

/-- Oplaxness of `subst` on `scr`: the outer `scr` structure threads
through pointwise, reusing the same source context and substitution pair
for every argument. Equality does not hold because the right-hand side
is strictly more permissive: each argument may carry an independent
decomposition. -/
theorem subst_scr_oplaxity (φ ψ : SynRel S) :
    subst (scr φ) ψ ≤ scr (subst φ ψ) := by
  intro Θ u v h
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hscr, hψ⟩ := h
  obtain ⟨g, ts, ss, rfl, rfl, hi⟩ := hscr
  refine ⟨g, fun i => (ts i).subst τ, fun i => (ss i).subst σ,
          by rw [hu]; rfl, by rw [hv]; rfl, fun i => ?_⟩
  exact ⟨Γ, ts i, ss i, τ, σ, rfl, rfl, hi i, hψ⟩

/-- `scr` preserves composition. The (≤) direction needs
`Classical.axiomOfChoice` to pick, per argument index, a middle term
witnessing the `φ * ψ` composition; the (≥) direction unfolds the two
`scr` witnesses and uses node injectivity to identify their operators
and argument vectors. -/
theorem scr_compositionality (φ ψ : SynRel S) : scr (φ * ψ) = scr φ * scr ψ := by
  ext Γ t v
  constructor
  · rintro ⟨g, ts, ss, rfl, rfl, hi⟩
    obtain ⟨us, hus⟩ := Classical.axiomOfChoice hi
    refine ⟨Tm.node g us, ?_, ?_⟩
    · exact ⟨g, ts, us, rfl, rfl, fun i => (hus i).1⟩
    · exact ⟨g, us, ss, rfl, rfl, fun i => (hus i).2⟩
  · rintro ⟨w, ⟨g₁, ts, ws, rfl, rfl, hi1⟩, ⟨g₂, ws', ss, hw₂, rfl, hi2⟩⟩
    obtain ⟨rfl, hws⟩ : g₁ = g₂ ∧ HEq ws ws' := by
      injection hw₂ with hg hws
      exact ⟨hg, hws⟩
    have hws' : ws = ws' := eq_of_heq hws
    subst hws'
    refine ⟨g₁, ts, ss, rfl, rfl, fun i => ?_⟩
    exact ⟨ws i, hi1 i, hi2 i⟩

/-- Fixed-point law: every term is either a variable or a node.
Algebraically, `Δη ⊔ tilde 1 = 1`. -/
theorem cr_fixpoint : (varDiag ⊔ scr 1 : SynRel S) = 1 := by
  ext Γ t s
  constructor
  · intro h
    rcases h with ⟨x, rfl, rfl⟩ | ⟨g, ts, ss, rfl, rfl, hi⟩
    · rfl
    · apply congrArg (Tm.node g)
      funext i
      exact hi i
  · intro (h : t = s)
    subst h
    induction t with
    | var x => exact Or.inl ⟨x, rfl, rfl⟩
    | node g ts _ => exact Or.inr ⟨g, ts, ts, rfl, rfl, fun _ => rfl⟩

/-- Structural induction: `Δη ⊔ tilde φ ≤ φ → 1 ≤ φ`. Proof is literal
`induction t`. -/
theorem cr_induction {φ : SynRel S}
    (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
  intro Γ t s (heq : t = s)
  subst heq
  induction t with
  | var x =>
    exact h Γ (Tm.var x) (Tm.var x) (Or.inl ⟨x, rfl, rfl⟩)
  | node g ts ih =>
    exact h Γ (Tm.node g ts) (Tm.node g ts)
      (Or.inr ⟨g, ts, ts, rfl, rfl, ih⟩)

/-! ### Group 3: the hard axioms

Two axioms about how *decompositions* of substituted forms compose, both
needing `Classical.choice` through `choose`. `subst_associativity` is the
technical peak of the file: its (≥) direction has to merge, into a single
source-context witness, the per-variable decompositions of
`(subst ψ χ).rel Δ (τ x) (σ x)`. Each `x : Γ` supplies its own context
`G x` with its own pre-substitution terms and substitutions; the natural
merged context is the **dependent sum** `Σ x : Γ, G x`, with
disjoint-image injections `inj x y := ⟨x, y⟩`. This is the payoff of
contexts-as-types (see Section 1): the merge closes via `Tm.subst_ren`
and `ψ.ren_closed` without any freshness bookkeeping, whereas a
finite-subsets presentation would need a fresh renaming per variable.
`subst_compositionality_oplax` is oplax rather than tight for the same
reason `subst_scr_oplaxity` is: the two factors on the RHS decompose
independently and there is nothing in the term algebra that merges them
back into a single decomposition witnessing the LHS. -/

/-- Associativity of relation substitution. The (≤) direction composes
the two substitutions via `Tm.subst_comp`; the (≥) direction merges the
per-variable decompositions of `(subst ψ χ)` into a single source
context via the dependent sum `Σ x : Γ, G x`, with disjoint-image
injections absorbing into the outer substitution by `Tm.subst_ren`. -/
theorem subst_associativity (φ ψ χ : SynRel S) :
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
    let τ₀ : Γ → Tm S Γ' := fun x => (TT x).ren (inj x)
    let σ₀ : Γ → Tm S Γ' := fun x => (SS x).ren (inj x)
    let τ₁ : Γ' → Tm S Δ := fun p => TA p.1 p.2
    let σ₁ : Γ' → Tm S Δ := fun p => SI p.1 p.2
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

/-- Oplaxness of `subst` on composition. The `choose` picks per-variable
middle terms `μ x` from the pointwise `(ψ * ψ')` witness; the middle
term of the outer composite is then `w.subst μ`. Reads as an inequality
because the RHS decomposes independently on each side of the outer
composition. -/
theorem subst_compositionality_oplax (φ φ' ψ ψ' : SynRel S) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro Δ u v h
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨Γ, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨Γ, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

/-! ### The closure constant `j` and its axioms

Under the advisor's revised presentation, `box` is no longer a primitive
`SRA` field but the derived operation `box a := j * a * j`, with `j` the
closure constant. Here we take `j` to be the identity restricted to
closed terms (the pair `(t, t)` where `t` is a weakening of some
`t₀ : Tm S Empty`) and discharge the four `j` axioms: co-reflexivity,
symmetry, co-transitivity, and orthogonality with `varDiag`. Under this
reading, `box a` unfolds to "the pairs of `a` whose two endpoints are
closed weakenings", which is strictly *different* from `subst a ⊥`; the
two agree on many relations (e.g. `a = ⊥`, `a = 1`) but not on all. -/

/-- The closure constant `j`: identity restricted to closed terms. Two
terms are `j`-related when they are equal AND weakenings of a closed
term. Renaming closure holds because a closed term stays closed under
renaming (`Tm.ren_close`). -/
def j : SynRel S := {
  rel := fun Γ t s => t = s ∧ ∃ t₀ : Tm S Empty, t = Tm.close Γ t₀
  ren_closed := by
    intro Γ Δ f t s h
    obtain ⟨hts, t₀, ht⟩ := h
    refine ⟨by rw [hts], t₀, ?_⟩
    rw [ht, Tm.ren_close]
}

/-- `j` at the level of `.rel`. -/
@[simp] theorem j_rel {Γ} {t s : Tm S Γ} :
    (j : SynRel S).rel Γ t s ↔
      t = s ∧ ∃ t₀ : Tm S Empty, t = Tm.close Γ t₀ :=
  Iff.rfl

/-- `j ≤ 1`: co-reflexive. The equality conjunct in `j` is exactly `1`. -/
theorem j_coreflexivity : (j : SynRel S) ≤ 1 := by
  intro Γ t s h
  exact h.1

/-- `jᵒ ≤ j`: symmetric. From `s = t` we get `t = s`, and the
closed-witness transports. -/
theorem j_symmetry : (j : SynRel S)ᵒ ≤ j := by
  intro Γ t s h
  obtain ⟨hst, t₀, hs⟩ := h
  exact ⟨hst.symm, t₀, hst.symm.trans hs⟩

/-- `j ≤ j * j`: co-transitive. Take the middle term to be `t` itself. -/
theorem j_cotransitivity : (j : SynRel S) ≤ j * j := by
  intro Γ t s h
  refine ⟨t, ⟨rfl, ?_⟩, h⟩
  obtain ⟨_, t₀, ht⟩ := h
  exact ⟨t₀, ht⟩

/-- `j * varDiag ≤ ⊥`: closed and variable are disjoint. The `varDiag`
witness forces the shared middle to be `Tm.var x`, while the `j` witness
forces it to be a weakened closed term. But a variable in an arbitrary
context is not the image of any closed term under `Empty.elim` (a closed
`Tm.var y` requires `y : Empty`, impossible; a closed `Tm.node` renames
to a `Tm.node`, not a `Tm.var`). -/
theorem j_varDiag_orthogonality : (j : SynRel S) * varDiag ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩ := h
  subst htu
  subst huvar
  cases t₀ with
  | var y => exact y.elim
  | node g ts => cases hcls

/-! ### The `subst · ⊥` characterisation: legacy reading of `□`

The two theorems in this block, `substBot_iff` and `substBot_mul`, are
the closed-form of `subst · ⊥` that used to discharge the axioms of the
primitive-`□` presentation (`□ := subst · ⊥`). Under the current
presentation `□ := j * · * j`, this is *not* the interpretation of `□`,
so these theorems no longer feed the `SRA` instance. They are retained
because they document the earlier reading and remain useful facts about
`subst · ⊥` per se. -/

/-- Closed-form characterisation of `subst a ⊥`: it relates `u` and `v`
iff they are the weakenings (`Tm.close Δ`) of an `a`-related pair of
closed terms. -/
theorem substBot_iff (a : SynRel S) {Δ} {u v : Tm S Δ} :
    (subst a ⊥ : SynRel S).rel Δ u v ↔
      ∃ (t s : Tm S Empty),
        u = Tm.close Δ t ∧ v = Tm.close Δ s ∧ a.rel Empty t s := by
  constructor
  · rintro ⟨Γ, t, s, τ, σ, rfl, rfl, ha, hbot⟩
    haveI : IsEmpty Γ := ⟨fun x => hbot x⟩
    let e : Γ → Empty := fun x => (hbot x).elim
    refine ⟨t.ren e, s.ren e, ?_, ?_, a.ren_closed e ha⟩
    · change t.subst τ = (t.ren e).ren Empty.elim
      rw [Tm.ren_ren]
      exact Tm.subst_empty t _ _
    · change s.subst σ = (s.ren e).ren Empty.elim
      rw [Tm.ren_ren]
      exact Tm.subst_empty s _ _
  · rintro ⟨t, s, rfl, rfl, ha⟩
    exact ⟨Empty, t, s, Tm.var ∘ Empty.elim, Tm.var ∘ Empty.elim,
           rfl, rfl, ha, fun e => e.elim⟩

/-- The `subst · ⊥` composition law: `subst (φ * ψ) ⊥ = subst φ ⊥ * subst ψ ⊥`.
The equality holds because both sides collapse to the same normal form,
an empty-context decomposition, via `Tm.ren_injective` applied to the
vacuously injective `Empty.elim`. -/
theorem substBot_mul (φ ψ : SynRel S) :
    (subst (φ * ψ) ⊥ : SynRel S) = subst φ ⊥ * subst ψ ⊥ := by
  ext Δ u v
  rw [substBot_iff]
  constructor
  · rintro ⟨t, s, rfl, rfl, w, hφ, hψ⟩
    refine ⟨Tm.close Δ w, ?_, ?_⟩
    · exact (substBot_iff φ).mpr ⟨t, w, rfl, rfl, hφ⟩
    · exact (substBot_iff ψ).mpr ⟨w, s, rfl, rfl, hψ⟩
  · rintro ⟨z, hφz, hψz⟩
    rw [substBot_iff] at hφz hψz
    obtain ⟨t₁, s₁, rfl, hz₁, hφ⟩ := hφz
    obtain ⟨t₂, s₂, hz₂, rfl, hψ⟩ := hψz
    have hinj : Function.Injective
        (fun t : Tm S Empty => t.ren (Empty.elim : Empty → Δ)) :=
      Tm.ren_injective _ (fun (e : Empty) _ _ => e.elim)
    have hst : s₁.ren (Empty.elim : Empty → Δ)
             = t₂.ren (Empty.elim : Empty → Δ) :=
      hz₁.symm.trans hz₂
    have h_eq : s₁ = t₂ := hinj hst
    subst h_eq
    exact ⟨t₁, s₂, rfl, rfl, s₁, hφ, hψ⟩

end SynRel

/-! ## Section 4: The `SRA` instance and non-degeneracy

With every axiom discharged in Section 3, the SRA typeclass instance is
pure assembly: each of the nineteen fields is bound to the corresponding
theorem, and the resulting `instSRA : SRA (SynRel S)` is what makes
every abstract lemma stated over `[SRA α]` apply directly to the term
model. From this point onward, the term-model side of every metatheorem
in the framework is a one-line instantiation.

Two non-degeneracy witnesses close the section. `scr_top_ne_bot` shows
that `scr` is not identically `⊥` as soon as the signature has *any*
operation symbol: the term `Tm.node f (fun _ => var ())` is `scr ⊤`
-related to itself, witnessing a concrete inhabitant of `scr ⊤ ≠ ⊥`.
`box_top_ne_bot` shows the same for `box ⊤` as soon as the signature has
a *nullary* operation (needed to inhabit `Tm S Empty` at all). These are
the sense in which the first-order model is genuinely non-trivial, in
contrast with the two-element consistency model of
`Instances/Consistency.lean` where both `scr` and `box` are forced to
collapse.

The section ends with the model-side verification of
`SRA.IsClosed (subst a j)`: for every `a`, the pointwise `j`-clause
inside `subst · j` forces both sides to be weakened closed terms, so
the whole relation lands in the image of `box`. This is the term-model
half of the "candidate axiom" record about the closure modality. -/

/-- The syntax relations on first-order `S`-terms form a `SRA`. -/
instance instSRA : SRA (SynRel S) where
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

variable {S : Signature}

/-- Non-degeneracy of `scr`: as long as `S` has an operation symbol,
`scr ⊤` is not `⊥`. Witness the term `Tm.node f (fun _ => Tm.var ())`
in `Tm S Unit`, which is `scr ⊤`-related to itself. Without any symbol,
every term is a variable and `scr φ = ⊥` for all `φ`, which is the
consistency-model collapse. -/
theorem scr_top_ne_bot (f : S.op) : (scr ⊤ : SynRel S) ≠ ⊥ := by
  intro hbad
  have h : (scr ⊤ : SynRel S).rel Unit
             (Tm.node f (fun _ => Tm.var ()))
             (Tm.node f (fun _ => Tm.var ())) :=
    ⟨f, _, _, rfl, rfl, fun _ => trivial⟩
  rw [hbad] at h
  exact h

/-- Non-degeneracy of `subst ⊤ ⊥` (i.e. `box ⊤`): as long as `S` has a
nullary operation symbol, this relation is not `⊥`. A closed term must
bottom out at a nullary node, and without one `Tm S Empty` is
uninhabited, forcing `box a = ⊥` for all `a`. -/
theorem box_top_ne_bot (f : S.op) (h : S.arity f = 0) :
    (subst (⊤ : SynRel S) ⊥) ≠ ⊥ := by
  intro hbad
  let t : Tm S Empty := Tm.node f (fun i => Fin.elim0 (h ▸ i))
  have hb : (subst (⊤ : SynRel S) ⊥).rel Unit
              (Tm.close Unit t) (Tm.close Unit t) :=
    ⟨Empty, t, t, Tm.var ∘ Empty.elim, Tm.var ∘ Empty.elim,
     rfl, rfl, trivial, fun e => e.elim⟩
  rw [hbad] at hb
  exact hb

/-- Model-side verification of `SRA.IsClosed (subst a j)`: for every
`a`, the pointwise `j`-clause in `subst · j` forces both sides to be
weakened closed terms, so the whole relation lands in the image of
`box`. Choice enters via `Classical.axiomOfChoice` to package the
per-variable closed witnesses. -/
theorem substJClosed (a : SynRel S) : SRA.IsClosed (SynRel.subst a j) := by
  change SynRel.subst a j ≤ SRA.box (SynRel.subst a j)
  intro Θ u v hsubst
  have hsub := hsubst
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, _, hj⟩ := hsub
  have hτσ : ∀ x, τ x = σ x := fun x => (hj x).1
  have hτ_cls : ∀ x, ∃ t₀ : Tm S Empty, τ x = Tm.close Θ t₀ :=
    fun x => (hj x).2
  obtain ⟨τ', hτ'eq⟩ := Classical.axiomOfChoice hτ_cls
  have hu_cls : (t.subst τ : Tm S Θ) = Tm.close Θ (t.subst τ') := by
    change t.subst τ = (t.subst τ').ren Empty.elim
    rw [Tm.ren_subst]
    congr 1
    funext x
    exact hτ'eq x
  have hv_cls : (s.subst σ : Tm S Θ) = Tm.close Θ (s.subst τ') := by
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

/-! ## Section 5: Confluence of orthogonal parallel reduction

The confluence chapter's payoff, on the term model.
`Metatheory/Confluence/Orthogonal.lean` proves `orthogonality_confluence`
for an arbitrary `[SRA α]`: if `a` is a reduction (`Δη * a ≤ ⊥`) and
satisfies the two orthogonality conjuncts, then its parallel closure
`a⇛` is confluent. Since Section 4 has established
`SRA (SynRel S)` for every first-order signature `S`, that abstract
theorem instantiates on the term model without any additional work: for
every `φ : SynRel S` verifying the same two local hypotheses, `parRed φ`
is confluent. Nothing new is proved here, and that is the whole point:
the abstract framework has done the job, and this file merely records
the corollary. -/

variable {S : Signature}

/-- Confluence of orthogonal reduction on the first-order term model.
Direct instantiation of `LeanTra.Confluence.orthogonality_confluence` at
the `SRA (SynRel S)` instance built in Section 4. -/
theorem confluent_parRed_synRel {φ : SynRel S}
    (h : LeanTra.Confluence.IsReduction φ)
    (horth : LeanTra.Confluence.IsOrthogonal φ) :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed φ) :=
  LeanTra.Confluence.orthogonality_confluence h horth

end LeanTra.Instances.FirstOrder

/-! ## Axiom trace

Explicit `#print axioms` commands on the main results of the file. Every
downstream theorem depends on `propext`, `Classical.choice`, and
`Quot.sound` (the three standard Lean-prelude axioms). No non-standard
assumption is required. -/

#print axioms LeanTra.Instances.FirstOrder.SynRel.instIsInvolutiveQuantale
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_varDiag_unit_right
#print axioms LeanTra.Instances.FirstOrder.SynRel.scr_compositionality
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_associativity
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_compositionality_oplax
#print axioms LeanTra.Instances.FirstOrder.instSRA
#print axioms LeanTra.Instances.FirstOrder.SynRel.substBot_mul
#print axioms LeanTra.Instances.FirstOrder.SynRel.substJClosed
#print axioms LeanTra.Instances.FirstOrder.confluent_parRed_synRel
