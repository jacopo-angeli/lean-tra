/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Instances.FirstOrder.Relations
public import LeanTra.Structure.SRA

/-!
# The three SRA operations on syntax relations — Phase C

Phase C of the LICS'26 term-model construction: defines the three
`SRA`-specific data — the variable co-equivalence `Δη` (`varDiag`), the
strict compatible refinement `ẽ·` (`scr`), and relation substitution
`·[·]` (`subst`) — on the carrier `SynRel S` built in Phase B,
discharges all sixteen `SRA` axioms, packages the result as a `SRA`
typeclass instance, and settles the (D-C7) box/composition question
the source leaves open at the axiom level.

## Contents

* `varDiag`, `scr`, `subst` — the three operations, each built with
  named-field syntax to sidestep the Phase-B implicit-lambda pitfall
  (see the "Pointwise lattice operations" section of `Relations.lean`).
* `varDiag_rel`, `scr_rel`, `subst_rel` — pointwise-semantics
  accessors, in the style of Phase B's `_rel` lemmas.
* Group 1 (easy axioms): monotonicity, converse-compatibility,
  join-preservation of `subst` in the first argument, symmetry of
  `varDiag`, its self-composition inequality, and the
  variable/node disjointness `varDiag * scr φ ≤ ⊥`.
* Group 2 (medium axioms): the two unit laws for substitution, the
  compatibility of `scr` with composition (`scr_mul`), the oplaxness
  law `subst (scr φ) ψ ≤ scr (subst φ ψ)`, the fixed-point law
  `varDiag ⊔ scr 1 = 1`, and structural induction
  `varDiag ⊔ scr φ ≤ φ → 1 ≤ φ`.
* Group 3 (the hard axioms): `subst_assoc` — associativity of relation
  substitution — via a dependent-sum merge (see (D-C5)); and
  `subst_mul_le` — oplaxness of substitution on composition — with the
  strictness note (D-C6).
* `instSRA` — the `SRA (SynRel S)` typeclass instance.
* Non-degeneracy: `scr_top_ne_bot` (needs a symbol) and `box_top_ne_bot`
  (needs a nullary symbol), certifying that the two SRA-specific
  operations do not collapse on this model — see (N1)/(N2).
* `box_iff` and `box_mul` — the closed-form characterisation of `box`
  and the equality `box (φ * ψ) = box φ * box ψ`, verified here in the
  term model; see (D-C7).

## Design decisions

### (D-C1) Substitution: two precisions vs. the paper

The paper (LICS'26 §3.1.1, Example 3(2)) states the pointwise
substitution clause as

  `Δ ⊢ t[τ] φ[ψ] s[σ] ⟺ ∃Γ. Δ ⊢ t φ s & ∀x ∈ Γ. Δ ⊢ τ(x) ψ σ(x)`

Two adjustments are needed to make it type correctly and admit multiple
decompositions of the same term:

1. **Contexts.** `t` and `s` are the pre-substitution terms, so they
   live in the *source* context `Γ`, not the target `Δ`. The premise
   is `Γ ⊢ t φ s`, not `Δ ⊢ t φ s` as the paper writes. This is a
   typo, corrected below.
2. **Decomposition.** The paper writes `t[τ]` and `s[σ]` as if the
   substituted forms and their decompositions were the same datum. In
   Lean, `u = t.subst τ` has many solutions in `(t, τ)` — pick a
   different variable partition and both `t` and `τ` change. Faithful
   formalisation quantifies existentially over the decomposition, with
   explicit equations `u = t.subst τ` in the body of the `∃`.

Both are recorded here as errata/precisions rather than deviations.

### (D-C2) `∃ (Γ : Type)` in a `Prop` — universe sanity

The definition of `subst` writes `∃ (Γ : Type) (t s : Tm S Γ) …` inside
the `rel` field, whose codomain is `Prop`. `Prop` is impredicative in
Lean 4, so `∃` over any `Sort` — including `Type` itself — lands in
`Prop`. The resulting `SynRel S` therefore stays at `Type 1`, and no
universe bump is triggered. A reader coming from a predicative
metatheory (Agda-style `Set₀` vs `Set₁`) will expect this to be a
problem; it is not.

### (D-C3) `subst_varDiag_right` is renaming closure

The proof of `subst φ varDiag = φ` is where the (D-B1) renaming-closure
field of `SynRel` earns its keep. The `varDiag` witnesses in the ψ-slot
force `τ x = σ x = Tm.var (ρ x)` for some `ρ : Γ → Δ`, so
`t.subst τ = t.ren ρ` and `s.subst σ = s.ren ρ` — the ≤ direction is
then a direct application of `φ.ren_closed ρ`. Without the closure
field the axiom fails, and the naïve context-free relation model
collapses at exactly this axiom. The reverse direction is trivial via
`Tm.subst_id`, taking `Γ := Δ` and `τ := σ := Tm.var`.

Extracting `ρ` from `∀ x, ∃ y, τ x = var y ∧ σ x = var y` requires
`Classical.axiomOfChoice`; this is the first axiom in the file to need
choice.

### (D-C4) `subst_scr_le` is strict, not an equality

`subst (scr φ) ψ ≤ scr (subst φ ψ)` is an inequality because the two
sides quantify decompositions differently: on the left, all argument
pairs share the same source context `Γ`, substitution pair `(τ, σ)`
and φ-witnesses (the "node" is decomposed once at the outer scr
witness); on the right, each argument pair `i` may carry its own
decomposition `(Γᵢ, tᵢ, sᵢ, τᵢ, σᵢ)`. The right-hand side is therefore
strictly more permissive, and equality does not hold in general.

### (D-C5) `subst_assoc` and the dependent-sum merge — payoff of (D1)

The (≥) direction of `subst_assoc` has to merge, into a single
source-context witness, the pointwise decompositions of
`(subst ψ χ).rel Δ (τ x) (σ x)`: each `x : Γ` supplies its own
context `G x` with `T x, S x : Tm S (G x)` and substitutions
`TA x, SI x : G x → Tm S Δ`. The natural merged context is the
**dependent sum** `Σ x : Γ, G x`, with injections
`inj x := fun y => ⟨x, y⟩`. Their images are automatically disjoint,
so the merged substitution `τ₁ p := TA p.1 p.2` inverts each
per-variable renaming without ever needing a freshness rename.

This is the payoff of (D1) in `Terms.lean`: contexts-as-types buys
disjoint-union-by-sigma at no cost. With contexts as finite subsets of
a global variable set, the same merge would require a fresh renaming
per `x`, and every downstream lemma would carry a freshness side
condition. Here `Sigma` closes the entire proof with `Tm.subst_ren`
and `ψ.ren_closed`, both already available.

### (D-C6) `subst_mul_le` is oplax, not tight

`subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ'` is one-directional
for the same reason (D-C4) is: reading the right-hand side as a
composition of two substitution relations, the two factors carry
*independent* decompositions — they need share neither a source context
nor a middle term — and there is nothing in the term algebra that
merges them back into a single decomposition witnessing the LHS. The
LHS pins the composite `(φ * φ')` inside one Γ and the pointwise
composite `(ψ * ψ')` at one shared middle term `μ x` per variable, so
it is strictly more restrictive.

### (D-C7) `box (φ * ψ) = box φ * box ψ` — the LICS'26 §3.2.1 question

LICS'26 §3.2.1 asserts the *equality* `□(a * b) = □a * □b`, but the
axioms only give the oplax half `□(a * b) ≤ □a * □b` (proved in
`Structure/Derived.lean`). The reverse direction cannot be derived —
it depends on a syntactic fact about the model.

This file proves the equality holds in the term model. The argument:
`(subst a ⊥).rel Δ u v` unfolds to a decomposition into a
`Tm S Γ`-pair over an *empty* source context — the last clause
`∀ x : Γ, ⊥.rel Δ (τ x) (σ x)` forces `Γ` uninhabited. So `box a`
relates two terms of `Tm S Δ` exactly when they are the weakenings of
an `a`-related pair of *closed* terms (`box_iff`). Once in that
normal form, `z = s₁.close Δ = t₂.close Δ` forces `s₁ = t₂` by
injectivity of weakening (`Tm.ren_injective` applied to the vacuously
injective `Empty.elim`), and the middle term of the composite reads
off immediately.

Verdict: equality holds in this model. Consequence for the source: the
law is a legitimate model fact but is **not** derivable from the SRA
axioms, so it must be **assumed** as an extra field (or an extra
structural property of the base algebra) if one wants it available in
the abstract theory. The oplax half `box_mul_le` is what generalises;
the tight half is a term-model witness.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. §3.1.1 and Example 3(2) supply the substitution clause
  corrected in (D-C1); the sixteen `SRA` axioms proved here follow the
  paper's listing.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.FirstOrder

namespace SynRel

variable {S : Signature}

/-! ## The three SRA operations -/

/-- The variable co-equivalence `Δη`: two terms are `varDiag`-related
when they are the same variable. Renaming closure is immediate — the
common variable transports to its `f`-image. -/
def varDiag : SynRel S := {
  rel := fun Γ t s => ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩
}

/-- Strict compatible refinement `ẽφ`: two terms are `scr φ`-related
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
`Θ`.

The paper writes the clause with two precisions we have to make
explicit — see (D-C1) in the module docstring. The `∃ (Γ : Type)` is a
Prop-level existential over `Type` and is fine by impredicativity of
`Prop` — see (D-C2). -/
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

/-! ## `.rel` accessors — pointwise semantics of each operation. -/

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

/-! ## Group 1 — the easy axioms. -/

/-- Monotonicity of `scr`. -/
theorem scr_mono {φ ψ : SynRel S} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro Γ t s hs
  obtain ⟨g, ts, ss, ht, hs', hi⟩ := hs
  exact ⟨g, ts, ss, ht, hs', fun i => h Γ (ts i) (ss i) (hi i)⟩

/-- Monotonicity of `subst` in the second argument. -/
theorem subst_mono_right {φ ψ ψ' : SynRel S} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro Θ u v hs
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨Γ, t, s, τ, σ, hu, hv, hφ, fun x => h Θ (τ x) (σ x) (hψ x)⟩

/-- `scr` commutes with converse. -/
theorem scr_converse (φ : SynRel S) : scr (φᵒ) = (scr φ)ᵒ := by
  ext Γ t s
  constructor
  · rintro ⟨g, ts, ss, rfl, rfl, hi⟩
    exact ⟨g, ss, ts, rfl, rfl, fun i => hi i⟩
  · rintro ⟨g, ts, ss, rfl, rfl, hi⟩
    exact ⟨g, ss, ts, rfl, rfl, fun i => hi i⟩

/-- Converse commutes with `subst`, swapping both arguments' converses. -/
theorem subst_converse (φ ψ : SynRel S) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

/-- `subst` preserves arbitrary joins in the first argument. -/
theorem subst_sSup_left (𝒮 : Set (SynRel S)) (ψ : SynRel S) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

/-- Symmetry of `varDiag`: swapping endpoints is absorbed. -/
theorem varDiag_converse_le : (varDiag : SynRel S)ᵒ ≤ varDiag := by
  intro Γ t s h
  obtain ⟨x, hs, ht⟩ := h
  exact ⟨x, ht, hs⟩

/-- Co-transitivity of `varDiag`: relating two variables through an
intermediate variable is direct. -/
theorem varDiag_le_mul_self : (varDiag : SynRel S) ≤ varDiag * varDiag := by
  intro Γ t s h
  obtain ⟨x, ht, hs⟩ := h
  exact ⟨Tm.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

/-- Variables and compound terms are disjoint: `Δη ; ẽφ` collapses to
`⊥`. Proof: the `varDiag` intermediate forces `u = Tm.var x`, while the
`scr` intermediate forces `u = Tm.node g ts` — impossible by
`Tm.noConfusion`. -/
theorem varDiag_mul_scr_le_bot (φ : SynRel S) :
    (varDiag : SynRel S) * scr φ ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨x, _, rfl⟩, ⟨g, ts, ss, hu, _, _⟩⟩ := h
  cases hu

/-! ## Group 2 — the medium axioms.

`subst_varDiag_right` is (D-C3); `subst_scr_le` is (D-C4); `scr_mul`
(≤) and `subst_varDiag_right` (≤) both need `Classical.axiomOfChoice`. -/

/-- `varDiag` is a left unit for `subst`: the `varDiag`-witness in the
first argument forces `t = s = Tm.var x`, and the substituted forms
become `τ x` and `σ x` which are directly ψ-related. Reverse direction
takes `Γ := Unit`, `t = s := Tm.var ()`. No choice needed. -/
theorem subst_varDiag_left (ψ : SynRel S) : subst varDiag ψ = ψ := by
  ext Θ u v
  constructor
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨Unit, Tm.var (), Tm.var (), fun _ => u, fun _ => v,
            rfl, rfl, ⟨(), rfl, rfl⟩, ?_⟩
    intro _; exact hψ

/-- `varDiag` is a right unit for `subst`. This is (D-C3): the
`varDiag` witnesses in the ψ-slot pin `τ` and `σ` to renamings
`Tm.var ∘ ρ`, so the substituted forms are `t.ren ρ` and `s.ren ρ`,
and the ≤ direction becomes `φ.ren_closed`. Extracting `ρ` from
`∀ x, ∃ y, τ x = var y ∧ σ x = var y` uses
`Classical.axiomOfChoice`. -/
theorem subst_varDiag_right (φ : SynRel S) : subst φ varDiag = φ := by
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

/-- Oplaxness of `subst` on `scr` — (D-C4): the outer `scr` structure
threads through pointwise, reusing the same source context and
substitution pair for every argument. Equality does not hold because
the right-hand side is strictly more permissive: each argument may
carry an independent decomposition. -/
theorem subst_scr_le (φ ψ : SynRel S) :
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
theorem scr_mul (φ ψ : SynRel S) : scr (φ * ψ) = scr φ * scr ψ := by
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
Algebraically, `Δη ⊔ ẽ1 = 1`. -/
theorem varDiag_sup_scr_one_eq : (varDiag ⊔ scr 1 : SynRel S) = 1 := by
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

/-- Structural induction: `Δη ⊔ ẽφ ≤ φ → 1 ≤ φ`. Proof is literal
`induction t`. -/
theorem one_le_of_scr_sup_le {φ : SynRel S}
    (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
  intro Γ t s (heq : t = s)
  subst heq
  induction t with
  | var x =>
    exact h Γ (Tm.var x) (Tm.var x) (Or.inl ⟨x, rfl, rfl⟩)
  | node g ts ih =>
    exact h Γ (Tm.node g ts) (Tm.node g ts)
      (Or.inr ⟨g, ts, ts, rfl, rfl, ih⟩)

/-! ## Group 3 — the hard axioms.

Both need `Classical.choice` (through `choose`) and both are strictly
about how *decompositions* of substituted forms compose. -/

/-- Associativity of relation substitution — (D-C5). The (≤) direction
composes the two substitutions via `Tm.subst_comp` and reuses the same
middle context throughout. The (≥) direction is the merge: `choose`
splits the pointwise `(subst ψ χ)` witnesses into families
`G, T, S, TA, SI` indexed by `Γ`, and the merged source context is the
dependent sum `Σ x : Γ, G x`. The disjoint-image injections
`inj x y := ⟨x, y⟩` absorb into the outer substitution via
`Tm.subst_ren`, and `ψ`'s renaming closure lifts the per-variable
witness to the merged context. -/
theorem subst_assoc (φ ψ χ : SynRel S) :
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

/-- Oplaxness of `subst` on composition — (D-C6). The `choose` picks
per-variable middle terms `μ x` from the pointwise `(ψ * ψ')` witness;
the middle term of the outer composite is then `w.subst μ`. Reads as an
inequality because the RHS decomposes independently on each side of the
outer composition (see (D-C6)). -/
theorem subst_mul_le (φ φ' ψ ψ' : SynRel S) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro Δ u v h
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨Γ, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨Γ, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

end SynRel

/-! ## The `SRA` typeclass instance.

All sixteen axioms are proved above; the instance simply forwards each
field. -/

/-- The syntax relations on first-order `S`-terms form a `SRA`. -/
instance instSRA : SRA (SynRel S) where
  varDiag := SynRel.varDiag
  scr := SynRel.scr
  subst := SynRel.subst
  varDiag_converse_le := SynRel.varDiag_converse_le
  varDiag_le_mul_self := SynRel.varDiag_le_mul_self
  scr_mono := fun _ _ h => SynRel.scr_mono h
  scr_mul := SynRel.scr_mul
  scr_converse := SynRel.scr_converse
  varDiag_mul_scr_le_bot := SynRel.varDiag_mul_scr_le_bot
  subst_mono_right := fun _ _ _ h => SynRel.subst_mono_right h
  subst_mul_le := SynRel.subst_mul_le
  subst_converse := SynRel.subst_converse
  subst_sSup_left := SynRel.subst_sSup_left
  subst_varDiag_left := SynRel.subst_varDiag_left
  subst_varDiag_right := SynRel.subst_varDiag_right
  subst_assoc := SynRel.subst_assoc
  subst_scr_le := SynRel.subst_scr_le
  varDiag_sup_scr_one_eq := SynRel.varDiag_sup_scr_one_eq
  one_le_of_scr_sup_le := fun _ h => SynRel.one_le_of_scr_sup_le h

namespace SynRel

/-! ## Non-degeneracy — (N1) and (N2).

Phase B showed the carrier is non-degenerate (`bot_ne_top`), but the
toy model also satisfies that. The two theorems below certify that the
SRA-specific operations do not collapse on this model — witness a
concrete non-triviality of `scr` and of `box`. Each requires a
hypothesis on the signature; without those hypotheses, the operations
*would* collapse (there being no non-variable term for `scr`, and no
closed term for `box`). -/

/-- (N1) `scr ⊤` is not `⊥` as long as `S` has an operation symbol —
witness the term `Tm.node f (fun _ => Tm.var ())` in `Tm S Unit`,
which is `scr ⊤`-related to itself. Without any symbol, every term is
a variable and `scr φ = ⊥` for all `φ` — the toy collapse. -/
theorem scr_top_ne_bot (f : S.op) : (scr ⊤ : SynRel S) ≠ ⊥ := by
  intro hbad
  have h : (scr ⊤ : SynRel S).rel Unit
             (Tm.node f (fun _ => Tm.var ()))
             (Tm.node f (fun _ => Tm.var ())) :=
    ⟨f, _, _, rfl, rfl, fun _ => trivial⟩
  rw [hbad] at h
  exact h

/-- (N2) `subst ⊤ ⊥` (i.e. `box ⊤`) is not `⊥` as long as `S` has a
nullary operation symbol — a closed term must bottom out at a nullary
node, and without one `Tm S Empty` is uninhabited, forcing `box a = ⊥`
for all `a`. -/
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

/-! ## The `box` law — (D-C7).

`box a := subst a ⊥`: relates `u v : Tm S Δ` exactly when both are
weakenings of an `a`-related pair over an *empty* source context. The
key lemma `box_iff` normalises the empty-context witness to
`Tm S Empty`, at which point `box_mul` follows from injectivity of
weakening (`Tm.ren_injective` on the vacuously injective `Empty.elim`)
— the two decompositions of the shared middle term `z` are forced to
agree. See (D-C7) for the modelling reading. -/

/-- Closed-form characterisation of `subst a ⊥`: it relates `u` and `v`
iff they are the weakenings (`Tm.close Δ`) of an `a`-related pair of
closed terms. The `→` direction repackages an arbitrary empty-context
witness as an `Empty`-context witness via renaming closure and
`Tm.subst_empty`; the `←` direction is direct with
`Γ := Empty`, `τ := σ := Tm.var ∘ Empty.elim`. -/
theorem box_iff (a : SynRel S) {Δ} {u v : Tm S Δ} :
    (subst a ⊥ : SynRel S).rel Δ u v ↔
      ∃ (t s : Tm S Empty),
        u = Tm.close Δ t ∧ v = Tm.close Δ s ∧ a.rel Empty t s := by
  constructor
  · rintro ⟨Γ, t, s, τ, σ, rfl, rfl, ha, hbot⟩
    -- hbot : ∀ x : Γ, False (through instBot)
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

/-- The box/composition law: `box (φ * ψ) = box φ * box ψ` in this
model — (D-C7). The oplax direction (`≤`) is `box_mul_le` in
`Structure/Derived.lean`; here we also prove `≥`, which forces
identifying the two empty-context decompositions of the shared middle
term `z` via `Tm.ren_injective`. Not derivable from the SRA axioms in
general (see the module docstring); this is a term-model witness that
the paper's asserted equality is legitimate as a *model* fact. -/
theorem box_mul (φ ψ : SynRel S) :
    (subst (φ * ψ) ⊥ : SynRel S) = subst φ ⊥ * subst ψ ⊥ := by
  ext Δ u v
  rw [box_iff]
  constructor
  · rintro ⟨t, s, rfl, rfl, w, hφ, hψ⟩
    refine ⟨Tm.close Δ w, ?_, ?_⟩
    · exact (box_iff φ).mpr ⟨t, w, rfl, rfl, hφ⟩
    · exact (box_iff ψ).mpr ⟨w, s, rfl, rfl, hψ⟩
  · rintro ⟨z, hφz, hψz⟩
    rw [box_iff] at hφz hψz
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

end LeanTra.Instances.FirstOrder

#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_varDiag_right
#print axioms LeanTra.Instances.FirstOrder.SynRel.scr_mul
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_assoc
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_mul_le
#print axioms LeanTra.Instances.FirstOrder.instSRA
#print axioms LeanTra.Instances.FirstOrder.SynRel.box_mul
