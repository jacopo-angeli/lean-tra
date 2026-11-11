/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Instances.Lambda.Relations
public import LeanTra.TRA.Basic

/-!
# The λ-calculus as a TRA

TRA operations on `TrmRel` and the verification of their twenty defining axioms.

## Main definitions
* `TrmRel.varDiag`, `TrmRel.scr`, `TrmRel.subst`, `TrmRel.j`: the four TRA operations.
* `TrmRel.introduction`, `TrmRel.elimination`: the two operational-decomposition pieces of `scr`,
  defined here so that `subst_scr_oplaxity`'s refutation can reference them.

## Main statements
* `TrmRel.instTRA`: the `TRA TrmRel` instance.
* `TrmRel.not_subst_scr_oplaxity_unguarded`: the unguarded `subst_scr_oplaxity` fails in this model.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale TRA

namespace LeanTra.Instances.Lambda
namespace TrmRel

/-! ## Section 3: TRA operations and their axioms

The heart of the file is the definition of the TRA operations and the
verification of their twenty defining axioms, culminating in
`instTRA : TRA TrmRel`. Four operations are needed. The diagonal
`varDiag` collects the equality on variables. The structural refinement
`scr` propagates a family of relations through the two term
constructors, so that `scr φ` relates `lam t` to `lam s` whenever `t`
and `s` are `φ`-related, and analogously for `app`; it is split into
two clauses to reflect the second-order signature, a `lam`-clause that
recurses at `Lam (n+1)` and an `app`-clause at the current arity.
Substitution `subst φ ψ` composes a relation on terms with a relation
on substitutions, delivering the standard fact that if `φ` relates `t`
and `s` and `ψ` relates two substitutions position by position then
the substituted terms are related. Finally `j` witnesses the finitary
join-preservation properties that the involutive quantale demands.
All twenty axioms are direct computations by induction on terms and
pattern-matching on renamings and substitutions; the two "oplaxity"
laws `subst_scr_oplaxity` and `subst_introduction_oplaxity` are
proved under the class-level guard `Δη ≤ ψ` (`Δη ≤ b`), and the
unguarded form of the first is refuted below in
`not_subst_scr_oplaxity_unguarded`, for reasons intrinsic to the de
Bruijn presentation and explained where those theorems live. -/

/-- `Δη`: pairs of the same variable. -/
def varDiag : TrmRel := {
  rel := fun n t s => ∃ x : Fin n, t = Lam.var x ∧ s = Lam.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩ }

/-- Strict compatible refinement: same outermost constructor with the
sub-terms pairwise related. `lam` clause demands the sub-relation at
the extended arity `n + 1`; `app` clause at the current arity. -/
def scr (φ : TrmRel) : TrmRel := {
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

/-- Relation substitution, same shape as the first-order case. -/
def subst (φ ψ : TrmRel) : TrmRel := {
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
def j : TrmRel := {
  rel := fun n t s => t = s ∧ ∃ t₀ : Lam 0, t = Lam.close n t₀
  ren_closed := by
    intro n m f t s h
    obtain ⟨hts, t₀, ht⟩ := h
    refine ⟨by rw [hts], t₀, ?_⟩
    rw [ht, Lam.ren_close] }

/-- `simp`-normal shape of `varDiag`. -/
@[simp] theorem varDiag_rel {n} {t s : Lam n} :
    (varDiag : TrmRel).rel n t s ↔ ∃ x : Fin n, t = Lam.var x ∧ s = Lam.var x :=
  Iff.rfl

/-- `simp`-normal shape of `scr`. -/
@[simp] theorem scr_rel {φ : TrmRel} {n} {t s : Lam n} :
    (scr φ).rel n t s ↔
      (∃ t' s', t = Lam.lam t' ∧ s = Lam.lam s' ∧ φ.rel (n + 1) t' s')
      ∨ (∃ t₁ t₂ s₁ s₂,
          t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
          ∧ φ.rel n t₁ s₁ ∧ φ.rel n t₂ s₂) := Iff.rfl

/-- `simp`-normal shape of `subst`. -/
@[simp] theorem subst_rel {φ ψ : TrmRel} {m} {u v : Lam m} :
    (subst φ ψ).rel m u v ↔
      ∃ (n : Nat) (t s : Lam n) (τ σ : Fin n → Lam m),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel n t s ∧ ∀ x, ψ.rel m (τ x) (σ x) := Iff.rfl

/-- `simp`-normal shape of `j`. -/
@[simp] theorem j_rel {n} {t s : Lam n} :
    (j : TrmRel).rel n t s ↔
      t = s ∧ ∃ t₀ : Lam 0, t = Lam.close n t₀ := Iff.rfl

/-! ### The easy axioms

Grouped here are the TRA axioms whose proof requires no genuine
insight, only a straightforward unfolding of the definitions of
`scr`, `subst`, and the involutive-quantale operations. Monotonicity
of `scr` and of `subst` in its second argument follows from the fact
that both are defined by an existential over a `φ`-obligation, so a
larger `φ` produces a larger existential. The commutation laws with
converse (`scr` and `subst`) are pattern-matches on the two clauses
of `scr` and a symmetric renaming of witnesses in `subst`. Join
preservation of `subst` in its first argument, the symmetry and
co-transitivity of the diagonal `varDiag`, and the orthogonality of
`varDiag` with `scr` (variables and compound terms are disjoint) all
close in the same style. Nothing here scales the wall of binders yet;
that is the job of the harder axioms further down. -/

/-- TRA axiom: monotonicity of `scr`. -/
theorem scr_monotonicity {φ ψ : TrmRel} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro n t s hs
  rcases hs with ⟨t', s', ht, hs', hφ⟩ | ⟨t₁, t₂, s₁, s₂, ht, hs', hφ₁, hφ₂⟩
  · exact Or.inl ⟨t', s', ht, hs', h _ _ _ hφ⟩
  · exact Or.inr ⟨t₁, t₂, s₁, s₂, ht, hs', h _ _ _ hφ₁, h _ _ _ hφ₂⟩

/-- TRA axiom: monotonicity of `subst` in its second argument. -/
theorem subst_monotonicity_right {φ ψ ψ' : TrmRel} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro m u v hs
  obtain ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨n, t, s, τ, σ, hu, hv, hφ, fun x => h m (τ x) (σ x) (hψ x)⟩

/-- TRA axiom: `scr` commutes with converse. -/
theorem scr_converse_commutation (φ : TrmRel) : scr (φᵒ) = (scr φ)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩
  · rintro (⟨t', s', rfl, rfl, hφ⟩ | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩)
    · exact Or.inl ⟨s', t', rfl, rfl, hφ⟩
    · exact Or.inr ⟨s₁, s₂, t₁, t₂, rfl, rfl, hφ₁, hφ₂⟩

/-- TRA axiom: converse commutes with `subst`, swapping both slots. -/
theorem subst_converse_commutation (φ ψ : TrmRel) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨n, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨n, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨n, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

/-- TRA axiom: `subst` preserves arbitrary joins in its first argument. -/
theorem subst_join_preservation_left (𝒮 : Set TrmRel) (ψ : TrmRel) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨n, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, n, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, n, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨n, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

/-- TRA axiom: `varDiag` is symmetric. -/
theorem varDiag_symmetry : (varDiag : TrmRel)ᵒ ≤ varDiag := by
  intro n t s ⟨x, hs, ht⟩; exact ⟨x, ht, hs⟩

/-- TRA axiom: `varDiag` is co-transitive. -/
theorem varDiag_cotransitivity : (varDiag : TrmRel) ≤ varDiag * varDiag := by
  intro n t s ⟨x, ht, hs⟩
  exact ⟨Lam.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

/-- TRA axiom: variables and compound terms are disjoint,
`varDiag * scr φ ≤ ⊥`. -/
theorem varDiag_scr_orthogonality (φ : TrmRel) :
    (varDiag : TrmRel) * scr φ ≤ ⊥ := by
  rintro n t v ⟨u, ⟨x, _, rfl⟩, h⟩
  rcases h with ⟨_, _, hu, _, _⟩ | ⟨_, _, _, _, hu, _, _, _⟩
  · cases hu
  · cases hu

/-! ### Unit laws for substitution

The two axioms saying that the diagonal on variables acts as a
two-sided unit for the relational substitution operator:
`subst varDiag ψ = ψ` and `subst φ varDiag = φ`. Together they are
the analogue, at the level of relations, of the classical fact that
substituting the identity substitution leaves a term unchanged; and
they are what lets the abstract TRA theory treat `subst` as a real
"substitution-shaped" operation. The left unit falls out immediately
by unfolding: the `varDiag` obligation on the first argument forces
the two substituted terms to be syntactically `var x`, and the
remaining pointwise `ψ`-obligation reduces to `ψ` itself. The right
unit is the delicate one, because the `varDiag` obligation on the
argument substitutions only tells us that each `τ x` and `σ x` are
*equal variables*, i.e. of the form `var (ρ x)` for some common `ρ`.
Extracting `ρ` uses classical choice and then the auxiliary lemma
`subst_var_eq_ren` (proved locally by induction on the term) collapses
substituting by such a "variable-valued" map into a renaming; ren-
closure of `φ` then closes the case. The lemma lives here rather
than up in Section 1 because this is the only place it is used. -/

/-- TRA axiom: `varDiag` is a left unit for `subst`. -/
theorem subst_varDiag_unit_left (ψ : TrmRel) : subst varDiag ψ = ψ := by
  ext m u v
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨1, Lam.var 0, Lam.var 0, fun _ => u, fun _ => v,
            rfl, rfl, ⟨0, rfl, rfl⟩, ?_⟩
    intro _; exact hψ

/-- Substituting `var (ρ x)` at every variable is renaming by `ρ`. Used to
collapse the pointwise `varDiag` obligation in `subst_varDiag_unit_right`
back onto `φ.ren_closed`; proved by induction on the term with the target
arity generalised so that the `lam` case works through `liftRen`. -/
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

/-- TRA axiom: `varDiag` is a right unit for `subst`. -/
theorem subst_varDiag_unit_right (φ : TrmRel) : subst φ varDiag = φ := by
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

/-! ### `scr` and composition

The interaction laws between the structural refinement `scr` and the
relational composition `*`, plus the associativity of `subst` and the
oplaxity of its interaction with composition. The key law is
`scr (φ * ψ) = scr φ * scr ψ`: propagating a composite relation
through a constructor is the same as composing the two structural
propagations. Together with `subst_associativity` and the oplax
inequality `subst φ ψ * subst φ' ψ' ≤ subst (φ * φ') (ψ * ψ')`, these
express that `scr` and `subst` are compatible with the monoidal
structure of the quantale in the expected way. The proofs are longer
than in the "easy" block only because a case analysis on the two
clauses of `scr` has to be threaded through the composition witness,
but each case is still a mechanical unfolding. -/

/-- TRA axiom: `scr` preserves composition. -/
theorem scr_compositionality (φ ψ : TrmRel) :
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

The two `OperationalDecomposition` operations are defined here so
that `subst_scr_oplaxity`'s block-level docstring and refutation can
reference them alongside the `scr` side of the story. Their axioms
(join preservation, compositionality, orthogonality, …) stay in
Section 4. -/

/-- Introduction forms: `(lam t, lam s)` with `a`-related bodies. -/
def introduction (a : TrmRel) : TrmRel := {
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
def elimination (a b : TrmRel) : TrmRel := {
  rel := fun n t s => ∃ t₁ t₂ s₁ s₂,
    t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
    ∧ a.rel n t₁ s₁ ∧ b.rel n t₂ s₂
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨t₁, t₂, s₁, s₂, ht, hs, ha, hb⟩ := h
    exact ⟨t₁.ren f, t₂.ren f, s₁.ren f, s₂.ren f,
           by rw [ht]; rfl, by rw [hs]; rfl,
           a.ren_closed f ha, b.ren_closed f hb⟩ }

/-- `simp`-normal shape of `introduction`. -/
@[simp] theorem introduction_rel {a : TrmRel} {n} {t s : Lam n} :
    (introduction a).rel n t s ↔ ∃ t' s',
      t = Lam.lam t' ∧ s = Lam.lam s' ∧ a.rel (n + 1) t' s' := Iff.rfl

/-- `simp`-normal shape of `elimination`. -/
@[simp] theorem elimination_rel {a b : TrmRel} {n} {t s : Lam n} :
    (elimination a b).rel n t s ↔ ∃ t₁ t₂ s₁ s₂,
      t = Lam.app t₁ t₂ ∧ s = Lam.app s₁ s₂
      ∧ a.rel n t₁ s₁ ∧ b.rel n t₂ s₂ := Iff.rfl

/-! ### The `subst_scr_oplaxity` guard, and why the unguarded form fails

The class field `TRA.subst_scr_oplaxity` takes an extra hypothesis
`Δη ≤ ψ`; this section explains why, and records a
machine-checked refutation of the unguarded statement in the
well-scoped de Bruijn model of this file.

The obstruction is entirely a symptom of the de Bruijn presentation.
At the `lam` clause of `scr`, the pointwise `ψ`-obligation of
substitution reaches the freshly-bound index `Fin.mk 0` of the
extended context, at which both lifted substitutions equal
`var 0`; the obligation on that position therefore reduces to
`ψ.rel _ (var 0) (var 0)`. If `ψ` does not relate `var 0` to
itself — the extreme case being `ψ = ⊥` — the obligation cannot be
discharged, and the LHS is inhabited by pairs (specifically the
closed-identity pair below) whose RHS witness is missing.

The concrete counterexample. Take `φ := ⊤`, `ψ := ⊥`, and consider
the pair `(t, s) := (λx.x, λx.x)` at arity `0`. The LHS
`subst (scr ⊤) ⊥` is inhabited via the decomposition `n₀ = 0`,
`t = λx.x`, `s = λx.x`, `τ = σ = elim0`, `hscr : scr ⊤ 0 (λx.x, λx.x)`
(the `lam` clause of `scr` at `⊤` is satisfied vacuously since `⊤`
holds everywhere), and the pointwise `ψ`-obligation is vacuously
true because `Fin 0` is empty. The RHS `scr (subst ⊤ ⊥)` at the
same pair requires `(subst ⊤ ⊥).rel 1 (var 0) (var 0)`, which
unfolds to `∃ n, t, s, τ, σ, var 0 = t.subst τ ∧ var 0 = s.subst σ
∧ … ∧ ∀ x, ⊥.rel 1 (τ x) (σ x)`; the last conjunct forces `n = 0`,
and then `var 0 = t.subst τ` with `t : Lam 0` and empty `τ` is
ruled out by `subst_closed_ne_var` (a substituted closed term is
never a variable, since `t : Lam 0` cannot be `var`).

The class field's guard `Δη ≤ ψ` excludes this counterexample from
the premise (at `ψ = ⊥`, the guard is unsatisfiable, since `Δη` is
inhabited by every `(var x, var x)`), and supplies the missing
ingredient at every other `ψ`: the fresh-position obligation
`ψ.rel _ (var 0) (var 0)` follows from `Δη ≤ ψ` and the `varDiag`
witness `⟨0, rfl, rfl⟩`; the `Fin.succ j` positions are discharged
by `ψ.ren_closed` applied to the original ψ-obligation.

Every use of the law in the abstract metatheory (see
`Metatheory/Confluence/ParallelReduction.lean` and `TRA/Howe.lean`)
instantiates `ψ` with a relation containing the identity (typically
`ψ = Δ` or `ψ = a⇛`); the guard is therefore satisfied at every
real call site. The first-order model in `PeanoArithmetic.lean`
proves the same law without the guard, because that syntax has no
binders and the fresh-position obligation never appears; the guard
is vacuous there. -/

/-- A substitution of a closed term is never a variable: `t : Lam 0` can
only be built from `app` or `lam` (never `var`, since `Fin 0` is empty),
and both of these are preserved by `subst`, so `t.subst τ` is never
`Lam.var x`. Key ingredient of `not_subst_scr_oplaxity_unguarded`. -/
theorem subst_closed_ne_var {m : Nat} (t : Lam 0) (τ : Fin 0 → Lam m) (x : Fin m) :
    t.subst τ ≠ Lam.var x := by
  cases t with
  | var i => exact i.elim0
  | app _ _ => intro h; cases h
  | lam _ => intro h; cases h

/-- Auxiliary: on the extended context `Fin (n+1)`, a lifted
substitution pair inherits its `ψ`-obligations from the underlying
pair via `ren_closed` on the `Fin.succ` positions, and from the
guard `Δη ≤ ψ` on the freshly-bound position (where both lifted
substitutions equal `var 0`). Used identically by
`subst_scr_oplaxity` and `subst_introduction_oplaxity` below. -/
theorem subst_liftSubst_ren_succ_of_le
    (ψ : TrmRel) {n m : Nat}
    (τ σ : Fin n → Lam m) (hψ : ∀ x, ψ.rel m (τ x) (σ x))
    (hvar : varDiag ≤ ψ) :
    ∀ i : Fin (n + 1),
      ψ.rel (m + 1) (Lam.liftSubst τ i) (Lam.liftSubst σ i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · -- Fresh position: `liftSubst _ 0 = var 0` on both sides;
    -- discharge via `Δη ≤ ψ`.
    have : (varDiag : TrmRel).rel (m + 1) (Lam.var 0) (Lam.var 0) :=
      ⟨0, rfl, rfl⟩
    exact hvar _ _ _ this
  · intro j
    -- Successor positions: `liftSubst _ (succ j) = (_ j).ren Fin.succ`.
    change ψ.rel (m + 1) ((τ j).ren Fin.succ) ((σ j).ren Fin.succ)
    exact ψ.ren_closed Fin.succ (hψ j)

/-- `TRA.subst_scr_oplaxity` in this model: with the guard `Δη ≤ ψ`,
substituting into a strict compatible refinement refines the strict
refinement of the substitution. Proof splits on the two clauses of
`scr` (the `lam` clause uses `subst_liftSubst_ren_succ_of_le` to lift
the ψ-obligation across the extra binder; the `app` clause inherits
the ψ-obligation unchanged). The unguarded form is refuted below
(`not_subst_scr_oplaxity_unguarded`); the block-level docstring
records the counterexample. -/
theorem subst_scr_oplaxity (φ ψ : TrmRel) (hvar : varDiag ≤ ψ) :
    subst (scr φ) ψ ≤ scr (subst φ ψ) := by
  rintro m u v ⟨n, u₀, v₀, τ, σ, rfl, rfl, hscr, hψ⟩
  rcases hscr with ⟨t', s', rfl, rfl, hφ⟩
                 | ⟨t₁, t₂, s₁, s₂, rfl, rfl, hφ₁, hφ₂⟩
  · -- lam clause: use `subst_liftSubst_ren_succ_of_le` to lift the
    -- ψ-obligation across the extra binder.
    refine Or.inl ⟨t'.subst (Lam.liftSubst τ), s'.subst (Lam.liftSubst σ),
                   rfl, rfl, ?_⟩
    exact ⟨n + 1, t', s', Lam.liftSubst τ, Lam.liftSubst σ,
           rfl, rfl, hφ,
           subst_liftSubst_ren_succ_of_le ψ τ σ hψ hvar⟩
  · -- app clause: no binder crossed, both sub-terms inherit the
    -- ψ-obligation unchanged.
    refine Or.inr ⟨t₁.subst τ, t₂.subst τ, s₁.subst σ, s₂.subst σ,
                    rfl, rfl, ?_, ?_⟩
    · exact ⟨n, t₁, s₁, τ, σ, rfl, rfl, hφ₁, hψ⟩
    · exact ⟨n, t₂, s₂, τ, σ, rfl, rfl, hφ₂, hψ⟩

/-- Refutation of the unguarded form. The pair `(λx.x, λx.x)` at
arity `0` lies in `subst (scr ⊤) ⊥` but not in `scr (subst ⊤ ⊥)`;
see the block-level docstring above for the argument, and
`subst_closed_ne_var` for the structural lemma the closing case
relies on. -/
theorem not_subst_scr_oplaxity_unguarded :
    ¬ ∀ φ ψ : TrmRel, subst (scr φ) ψ ≤ scr (subst φ ψ) := by
  intro h
  have hL : (subst (scr ⊤) ⊥).rel 0 (Lam.lam (Lam.var 0)) (Lam.lam (Lam.var 0)) :=
    ⟨0, Lam.lam (Lam.var 0), Lam.lam (Lam.var 0), Fin.elim0, Fin.elim0, rfl, rfl,
     Or.inl ⟨Lam.var 0, Lam.var 0, rfl, rfl, trivial⟩, fun x => x.elim0⟩
  rcases h ⊤ ⊥ 0 _ _ hL with ⟨t', _, ht, _, hsub⟩ | ⟨_, _, _, _, ht, _, _, _⟩
  · have heq : Lam.var 0 = t' := Lam.lam.inj ht
    subst heq
    obtain ⟨n, t, _, τ, _, hu, _, _, hψ⟩ := hsub
    cases n with
    | zero => exact subst_closed_ne_var t τ 0 hu.symm
    | succ n => exact (hψ 0).elim
  · cases ht

theorem subst_associativity (φ ψ χ : TrmRel) :
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
  · -- (≥) direction: Σ-context concatenation.
    -- Each `x : Fin n₀` contributes a local context of arity `k(x) = n₁(x)`;
    -- the global context is `Σ x, k(x)` (encoded as `Fin (∑ x, k(x))`).
    rintro ⟨n₀, t₀, s₀, τ₀, σ₀, rfl, rfl, hφ, hpsi_chi⟩
    -- Extract per-variable local witnesses via choice.
    choose k t₁ s₁ μ ν hτ hσ hψ hχ using hpsi_chi
    -- The global arity: sum of all local arities.
    let N : Nat := ∑ x : Fin n₀, k x
    -- Coordinate injection: pack (x, j) into a Fin N.
    let ι : (x : Fin n₀) → Fin (k x) → Fin N :=
      fun x j => finSigmaFinEquiv ⟨x, j⟩
    -- The global term: substitute each variable of `t₀` by the ren-embedded
    -- local witness, and analogously for `s₀`.
    refine ⟨N, t₀.subst (fun x => (t₁ x).ren (ι x)),
                s₀.subst (fun x => (s₁ x).ren (ι x)),
            fun y => (μ (finSigmaFinEquiv.symm y).1 (finSigmaFinEquiv.symm y).2),
            fun y => (ν (finSigmaFinEquiv.symm y).1 (finSigmaFinEquiv.symm y).2),
            ?_, ?_, ?_, ?_⟩
    · -- u = (t₀.subst (fun x => (t₁ x).ren (ι x))).subst μ'
      rw [Lam.subst_comp]
      apply congrArg t₀.subst
      funext x
      rw [Lam.subst_ren, hτ x]
      apply congrArg (t₁ x).subst
      funext j
      show μ x j = μ (finSigmaFinEquiv.symm (ι x j)).1
                     (finSigmaFinEquiv.symm (ι x j)).2
      have hinv : finSigmaFinEquiv.symm (ι x j) = ⟨x, j⟩ :=
        finSigmaFinEquiv.symm_apply_apply ⟨x, j⟩
      rw [hinv]
    · rw [Lam.subst_comp]
      apply congrArg s₀.subst
      funext x
      rw [Lam.subst_ren, hσ x]
      apply congrArg (s₁ x).subst
      funext j
      show ν x j = ν (finSigmaFinEquiv.symm (ι x j)).1
                     (finSigmaFinEquiv.symm (ι x j)).2
      have hinv : finSigmaFinEquiv.symm (ι x j) = ⟨x, j⟩ :=
        finSigmaFinEquiv.symm_apply_apply ⟨x, j⟩
      rw [hinv]
    · -- (subst φ ψ).rel N T S
      refine ⟨n₀, t₀, s₀,
              fun x => (t₁ x).ren (ι x), fun x => (s₁ x).ren (ι x),
              rfl, rfl, hφ, ?_⟩
      intro x
      exact ψ.ren_closed (ι x) (hψ x)
    · -- ∀ y, χ.rel m (μ' y) (ν' y)
      intro y
      exact hχ _ _

theorem subst_compositionality_oplax (φ φ' ψ ψ' : TrmRel) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro m u v h
  obtain ⟨n, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨n, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨n, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

/-- TRA axiom: fixed-point law `varDiag ⊔ scr 1 = 1`, every term is
either a variable or a compound. -/
theorem cr_fixpoint : (varDiag ⊔ scr 1 : TrmRel) = 1 := by
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

/-- TRA axiom: structural induction, `varDiag ⊔ scr φ ≤ φ` implies
`1 ≤ φ`. -/
theorem cr_induction {φ : TrmRel} (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
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

/-- TRA axiom: `j` is co-reflexive. -/
theorem j_coreflexivity : (j : TrmRel) ≤ 1 := fun _ _ _ h => h.1

/-- TRA axiom: `j` is symmetric. -/
theorem j_symmetry : (j : TrmRel)ᵒ ≤ j := by
  intro n t s h
  obtain ⟨hst, t₀, hs⟩ := h
  exact ⟨hst.symm, t₀, hst.symm.trans hs⟩

/-- TRA axiom: `j` is co-transitive. -/
theorem j_cotransitivity : (j : TrmRel) ≤ j * j := by
  intro n t s h
  refine ⟨t, ⟨rfl, ?_⟩, h⟩
  obtain ⟨_, t₀, ht⟩ := h
  exact ⟨t₀, ht⟩

/-- TRA axiom: closed terms and variables are disjoint,
`j * varDiag ≤ ⊥`. -/
theorem j_varDiag_orthogonality : (j : TrmRel) * varDiag ≤ ⊥ := by
  intro n t v ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩
  subst htu; subst huvar
  -- hcls : Lam.var x = Lam.close n t₀; case on t₀'s constructor.
  cases t₀ with
  | var y => exact y.elim0
  | app _ _ => cases hcls
  | lam _ => cases hcls

/-! ### The TRA instance

The point at which all the preceding work becomes usable. Everything
above amounts to twenty theorems named `varDiag_symmetry`,
`scr_compositionality`, `subst_associativity`, and so on; here we
bind them to the corresponding fields of the `TRA` typeclass so that
`instTRA : TRA TrmRel` is inhabited. From this line onward, every
abstract lemma stated in the `TRA` layer of the framework applies
directly to `TrmRel`, without any further manual work: this is the
interface between the concrete syntactic world of `Lam` and the
abstract metatheory of Term Relation Algebras. The instance itself
is pure typeclass assembly and carries no mathematical content, but
its existence is what makes the whole file a genuine instance of the
framework rather than a parallel development. -/

/-- The syntax relations on well-scoped λ-terms form an `TRA`. -/
instance instTRA : TRA TrmRel where
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

end TrmRel
end LeanTra.Instances.Lambda
