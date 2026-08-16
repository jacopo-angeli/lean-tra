/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Instances.FirstOrder.Relations
public import LeanTra.SRA.Basic
public import LeanTra.SRA.Basic
public import LeanTra.SRA.Modality

/-!
# The three SRA operations on syntax relations

Phase C of the LICS'26 term-model construction: defines the four
`SRA`-specific data — the variable co-equivalence `Δη` (`varDiag`), the
strict compatible refinement `tilde ·` (`scr`), relation substitution
`·[·]` (`subst`), and the closure constant `j` (identity on closed
terms) — on the carrier `SynRel S` built in Phase B, discharges all
`SRA` axioms (the fifteen for the first three data plus the four for
`j`), and packages the result as a `SRA` typeclass instance. The
derived modality `box := j * · * j` is *not* the same operation as
`subst · ⊥`; the earlier `subst · ⊥` normal-form theorems
(`substBot_iff`, `substBot_mul`) are retained here as facts about
`subst · ⊥` per se — see the block-level docstring inside the file.

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
  compatibility of `scr` with composition (`scr_compositionality`), the oplaxness
  law `subst (scr φ) ψ ≤ scr (subst φ ψ)`, the fixed-point law
  `varDiag ⊔ scr 1 = 1`, and structural induction
  `varDiag ⊔ scr φ ≤ φ → 1 ≤ φ`.
* Group 3 (the hard axioms): `subst_associativity` — associativity of relation
  substitution — via a dependent-sum merge (see (D-C5)); and
  `subst_compositionality_oplax` — oplaxness of substitution on composition — with the
  strictness note (D-C6).
* `j`, `j_rel`, `j_coreflexivity`, `j_symmetry`, `j_cotransitivity`,
  `j_varDiag_orthogonality` — the closure constant and its four axioms.
* `substBot_iff` and `substBot_mul` — legacy `subst · ⊥` normal-form
  theorems, kept as documentation of the earlier `box := subst · ⊥`
  reading. NOT the interpretation of the current derived `box`.
* `instSRA` — the `SRA (SynRel S)` typeclass instance.
* Non-degeneracy: `scr_top_ne_bot` (needs a symbol) and `box_top_ne_bot`
  (needs a nullary symbol), certifying that the two SRA-specific
  operations do not collapse on this model — see (N1)/(N2).

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

### (D-C3) `subst_varDiag_unit_right` is renaming closure

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

### (D-C4) `subst_scr_oplaxity` is strict, not an equality

`subst (scr φ) ψ ≤ scr (subst φ ψ)` is an inequality because the two
sides quantify decompositions differently: on the left, all argument
pairs share the same source context `Γ`, substitution pair `(τ, σ)`
and φ-witnesses (the "node" is decomposed once at the outer scr
witness); on the right, each argument pair `i` may carry its own
decomposition `(Γᵢ, tᵢ, sᵢ, τᵢ, σᵢ)`. The right-hand side is therefore
strictly more permissive, and equality does not hold in general.

### (D-C5) `subst_associativity` and the dependent-sum merge — payoff of (D1)

The (≥) direction of `subst_associativity` has to merge, into a single
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

### (D-C6) `subst_compositionality_oplax` is oplax, not tight

`subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ'` is one-directional
for the same reason (D-C4) is: reading the right-hand side as a
composition of two substitution relations, the two factors carry
*independent* decompositions — they need share neither a source context
nor a middle term — and there is nothing in the term algebra that
merges them back into a single decomposition witnessing the LHS. The
LHS pins the composite `(φ * φ')` inside one Γ and the pointwise
composite `(ψ * ψ')` at one shared middle term `μ x` per variable, so
it is strictly more restrictive.

### (D-C7) The `substBot_mul` equality — legacy note

LICS'26 §3.2.1 originally read `□a := a[⊥]`, and this file's
`substBot_iff` / `substBot_mul` witness the equality
`(a * b)[⊥] = a[⊥] * b[⊥]` in the term model — an equality that is
not derivable from the abstract `SRA` axioms. Under the current
presentation, `□ := j * · * j` is not the same operation as `· [⊥]`,
so this equality no longer speaks to the `SRA` theorem
`box_compositionality_lax : □R * □S ≤ □(R * S)` (the only surviving half of
LICS'26 §3.2.1's asserted equality — the reverse direction is refuted;
see `SynRel.not_box_mul_le_mul_box` and the "Open questions"
section of `SRA/Modality.lean`). The two `substBot_*` theorems
are retained as facts about `subst · ⊥` per se; see the block-level
docstring at their definition.

Sanity note on the dropped axiom `box_subst_le : subst (box a) b ≤
box a`. Under the OLD reading `□a := a[⊥]`, this becomes
`subst (subst a ⊥) b ≤ subst a ⊥`, which is in fact an EQUALITY via
`subst_associativity` and `subst_bot_strictness_left` (`subst (subst a ⊥) b =
subst a (subst ⊥ b) = subst a ⊥`); it holds *abstractly*, not merely
in the term model. Under the NEW reading `□ := j * · * j`, the same
statement `subst (j * a * j) b ≤ j * a * j` is neither derivable nor
true in the term model — this is the actual reason the axiom was
dropped, and the counterexample lives in `Structure/Derived.lean`'s
Investigation block on `box_subst_le`.

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
`scr` intermediate forces `u = Tm.node g ts` — impossible by
`Tm.noConfusion`. -/
theorem varDiag_scr_orthogonality (φ : SynRel S) :
    (varDiag : SynRel S) * scr φ ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨x, _, rfl⟩, ⟨g, ts, ss, hu, _, _⟩⟩ := h
  cases hu

/-! ## Group 2 — the medium axioms.

`subst_varDiag_unit_right` is (D-C3); `subst_scr_oplaxity` is (D-C4); `scr_compositionality`
(≤) and `subst_varDiag_unit_right` (≤) both need `Classical.axiomOfChoice`. -/

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

/-- `varDiag` is a right unit for `subst`. This is (D-C3): the
`varDiag` witnesses in the ψ-slot pin `τ` and `σ` to renamings
`Tm.var ∘ ρ`, so the substituted forms are `t.ren ρ` and `s.ren ρ`,
and the ≤ direction becomes `φ.ren_closed`. Extracting `ρ` from
`∀ x, ∃ y, τ x = var y ∧ σ x = var y` uses
`Classical.axiomOfChoice`. -/
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

/-- Oplaxness of `subst` on `scr` — (D-C4): the outer `scr` structure
threads through pointwise, reusing the same source context and
substitution pair for every argument. Equality does not hold because
the right-hand side is strictly more permissive: each argument may
carry an independent decomposition. -/
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

/-- Oplaxness of `subst` on composition — (D-C6). The `choose` picks
per-variable middle terms `μ x` from the pointwise `(ψ * ψ')` witness;
the middle term of the outer composite is then `w.subst μ`. Reads as an
inequality because the RHS decomposes independently on each side of the
outer composition (see (D-C6)). -/
theorem subst_compositionality_oplax (φ φ' ψ ψ' : SynRel S) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro Δ u v h
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨Γ, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨Γ, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

/-! ## The closure constant `j` and its axioms.

Under the advisor's revised presentation, `box` is no longer a primitive
`SRA` field but the *derived* operation `box a := j * a * j`, with `j` the
closure constant (see `Structure/SRA.lean`). Here we take `j` to be the
identity restricted to closed terms — the pair `(t, t)` where `t` is a
weakening of some `t₀ : Tm S Empty` — and discharge the four `j`
axioms.

Under this reading, `box a` (unfolded) becomes "the pairs of `a` whose
two endpoints are closed weakenings", which is strictly *different* from
`subst a ⊥`. The two agree on many relations (e.g. `a = ⊥`, `a = 1`) but
not on all: the `SynRel a Γ t s := Nonempty Γ` witness in
`Structure/Derived.lean`'s design note is `subst a ⊥ = ⊥` yet
`box a Unit = Unit-closed pairs`. Consequently the old
`box_iff` / `box_mul` characterisation is *about `subst · ⊥`, not about
the new `box`*; the two theorems are kept below under the names
`substBot_iff` / `substBot_mul` and their docstrings updated. -/

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
forces it to be a weakened closed term — but a variable in an arbitrary
context is not the image of any closed term under `Empty.elim` (a closed
`Tm.var y` requires `y : Empty`, impossible; a closed `Tm.node` renames
to a `Tm.node`, not a `Tm.var`). -/
theorem j_varDiag_orthogonality : (j : SynRel S) * varDiag ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩ := h
  subst htu
  subst huvar
  -- hcls : Tm.var x = Tm.close Γ t₀
  cases t₀ with
  | var y => exact y.elim
  | node g ts => cases hcls

/-! ## The `subst · ⊥` characterisation — legacy reading of `□`.

The two theorems in this block, `substBot_iff` and `substBot_mul`, are
the closed-form of `subst · ⊥` that used to discharge the axioms of the
primitive-`□` presentation (`□ := subst · ⊥`). Under the current
presentation `□ := j * · * j`, this is *not* the interpretation of `□`,
so these theorems no longer feed the `SRA` instance. They are retained
because they document the earlier reading and remain useful facts about
`subst · ⊥` per se. -/

/-- Closed-form characterisation of `subst a ⊥`: it relates `u` and `v`
iff they are the weakenings (`Tm.close Δ`) of an `a`-related pair of
closed terms. The `→` direction repackages an arbitrary empty-context
witness as an `Empty`-context witness via renaming closure and
`Tm.subst_empty`; the `←` direction is direct with
`Γ := Empty`, `τ := σ := Tm.var ∘ Empty.elim`. Was `box_iff` when
`box := subst · ⊥`. -/
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
Was `box_mul` when `box := subst · ⊥`. The equality holds because both sides
collapse to the same normal form — an empty-context decomposition — via
`Tm.ren_injective` applied to the vacuously injective `Empty.elim`. -/
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

/-! ## The `SRA` typeclass instance.

All nineteen axioms — the fifteen for `Δη`, `scr`, `subst` plus the four
for the closure constant `j` — are proved above; the instance simply
forwards each field. -/

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

/-! ## Experiment 3(c) — `T[j]` is closed in the term model.

Model verification of `SRA.SubstJClosed` (see `Structure/Derived.lean`):
for every `a : SynRel S`, `subst a j` is closed. The argument: the
pointwise clause `∀ x, j.rel Θ (τ x) (σ x)` in the definition of
`subst · j` forces `τ = σ` and every `τ x` a weakened closed term.
Substituting closed terms into every variable of a term yields another
weakened closed term (a `Tm.ren_subst` argument through
`Empty.elim`), so both endpoints `u = t.subst τ` and `v = s.subst σ`
of the resulting pair are themselves weakened closed terms — exactly
the shape needed for membership in `SRA.box (subst a j) =
j * (subst a j) * j` with middle witnesses `u` and `v`. -/

/-- The advisor's third suggestion, verified for `SynRel S`:
`IsClosed (subst a j)` for every `a`. Proof witnesses: each `x : Γ`
supplies (via the pointwise `j`-clause) a closed term `τ' x : Tm S Empty`
with `τ x = Tm.close Θ (τ' x)`; then
`u = t.subst τ = Tm.close Θ (t.subst τ')` by `Tm.ren_subst`, and
similarly for `v` using `τ = σ`. Choice enters via
`Classical.axiomOfChoice` to package the per-variable `τ' x`.

Together with the abstract `SRA.SubstJClosed` predicate, this
theorem is the model-side half of the "candidate axiom" record: the
axiom holds where it matters. -/
theorem substJClosed (a : SynRel S) : SRA.IsClosed (SynRel.subst a j) := by
  change SynRel.subst a j ≤ SRA.box (SynRel.subst a j)
  intro Θ u v hsubst
  have hsub := hsubst
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, _, hj⟩ := hsub
  -- `hsubst : (subst a j).rel Θ (t.subst τ) (s.subst σ)` (unchanged; the
  -- destructuring was on the copy `hsub`).
  have hτσ : ∀ x, τ x = σ x := fun x => (hj x).1
  have hτ_cls : ∀ x, ∃ t₀ : Tm S Empty, τ x = Tm.close Θ t₀ :=
    fun x => (hj x).2
  obtain ⟨τ', hτ'eq⟩ := Classical.axiomOfChoice hτ_cls
  -- τ' : Γ → Tm S Empty, hτ'eq : ∀ x, τ x = Tm.close Θ (τ' x)
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
  -- Goal: (SRA.box (subst a j)).rel Θ (t.subst τ) (s.subst σ)
  --   = ((j * (subst a j)) * j).rel Θ (t.subst τ) (s.subst σ)
  -- Witnesses: outer middle `s.subst σ`, inner middle `t.subst τ`.
  refine ⟨s.subst σ, ⟨t.subst τ,
          ⟨rfl, t.subst τ', hu_cls⟩,
          hsubst⟩,
          ⟨rfl, s.subst τ', hv_cls⟩⟩

end SynRel

end LeanTra.Instances.FirstOrder

#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_varDiag_unit_right
#print axioms LeanTra.Instances.FirstOrder.SynRel.scr_compositionality
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_associativity
#print axioms LeanTra.Instances.FirstOrder.SynRel.subst_compositionality_oplax
#print axioms LeanTra.Instances.FirstOrder.instSRA
#print axioms LeanTra.Instances.FirstOrder.SynRel.substBot_mul
#print axioms LeanTra.Instances.FirstOrder.SynRel.substJClosed
