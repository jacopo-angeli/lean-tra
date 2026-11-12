/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Instances.Peano.Relations
public import LeanTra.TRA.Basic
public import LeanTra.TRA.Modality

/-!
# Peano arithmetic as a TRA

TRA operations on `TrmRel` and the verification of their twenty defining axioms.

## Main definitions
* `TrmRel.varDiag`, `TrmRel.scr`, `TrmRel.subst`, `TrmRel.j`: the four TRA operations.

## Main statements
* `instTRA`: the `TRA TrmRel` instance.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.PeanoArithmetic
namespace TrmRel

/-!
`TrmRel` is now an involutive quantale, so we can define the four
operations the `TRA` typeclass demands and start discharging their
axioms. The four operations are `varDiag` (the variable co-equivalence,
which relates two terms iff they are the same variable), `scr` (the
strict compatible refinement, which relates two terms iff they have the
same outermost constructor with pairwise `φ`-related sub-terms), `subst`
(relation substitution, the categorical action of substitutions on
relations), and `j` (the closure constant, which relates a term to
itself provided the term is the weakening of a closed term).

Between the four operations the TRA class prescribes twenty axioms,
which we discharge in three passes ordered by technical difficulty. The
first pass — monotonicity, commutation with converse, join-preservation
in the second slot of `subst`, symmetry and co-transitivity of `varDiag`
— is unfolding and symbol-pushing. The second pass needs some real work:
`subst_varDiag_unit_right` requires `Classical.axiomOfChoice` to extract
a common renaming from a pointwise-varDiag substitution;
`scr_compositionality` is a sixteen-case diagram chase; `cr_fixpoint`
and `cr_induction` collapse to structural induction on `Tm`. The third
pass carries the two conceptually hard theorems: associativity of
substitution, whose ⇐-direction forces us to glue two intermediate
contexts into a dependent sum `Σ (x : Γ), G x` to fit the single-context
statement, and oplax compositionality, whose ⇒-direction uses
`Classical.axiomOfChoice` to select a shared intermediate substitution
at each variable. The section closes with the four axioms governing
`j`, which are immediate once one recognises `j` as the intersection of
the diagonal with "term is the weakening of a closed one".
-/

/-- The variable co-equivalence (paper: `Δη`): relates `t` and `s` iff
both are the same variable `Tm.var x`. Sees only variables and ignores
compound terms; serves as the two-sided identity of relation
substitution and is orthogonal to every compound-headed relation. -/
def varDiag : TrmRel := {
  rel := fun Γ t s => ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x
  ren_closed := by
    intro _ _ f _ _ h
    obtain ⟨x, ht, hs⟩ := h
    exact ⟨f x, by rw [ht]; rfl, by rw [hs]; rfl⟩
}

/-- Strict compatible refinement (paper: `~φ`): relates `t` and `s`
iff they have the same outermost constructor and their immediate
sub-terms are pairwise `φ`-related. Four disjuncts, one per
constructor: `(zero, zero)` with no premise on `φ` (nullary intro),
`(succ t', succ s')` with `φ t' s'` (unary intro),
`(plus m₁ n₁, plus m₂ n₂)` and `(mult m₁ n₁, mult m₂ n₂)` with
pairwise-`φ` bodies (binary elim). The nullary case is precisely what
makes `scr ⊥ ≠ ⊥` and forces the non-empty-join relaxation of
`OperationalDecomposition` discussed in the module preamble. -/
def scr (φ : TrmRel) : TrmRel := {
  rel := fun Γ t s =>
    (t = Tm.zero ∧ s = Tm.zero) ∨
    (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ φ.rel Γ t' s') ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                            φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                            φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂)
  ren_closed := by
    intro Γ Δ f t s h
    rcases h with ⟨rfl, rfl⟩
                | ⟨t', s', rfl, rfl, hφ⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨t'.ren f, s'.ren f, rfl, rfl, φ.ren_closed f hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    rfl, rfl, φ.ren_closed f hφm, φ.ren_closed f hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    rfl, rfl, φ.ren_closed f hφm, φ.ren_closed f hφn⟩))
}

/-- Relation substitution (paper: `φ[ψ]`): relates `u` and `v` at
context Θ when there exist a source context Γ, terms `t s : Tm Γ` with
`φ.rel Γ t s`, and substitutions `τ σ : Γ → Tm Θ` with `τ x` and `σ x`
pointwise `ψ`-related, such that `u = t.subst τ` and `v = s.subst σ`.
The source context Γ is existentially quantified — a witness, not part
of the data — which is why associativity of `subst` needs to glue two
such witnesses into a dependent sum below. -/
def subst (φ ψ : TrmRel) : TrmRel := {
  rel := fun Θ u v =>
    ∃ (Γ : Type) (t s : Tm Γ) (τ σ : Γ → Tm Θ),
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

/-!
Projection lemmas that unfold each of the three operations back to
their `Prop`-level content, tagged `@[simp]` for automated use.
-/

@[simp] theorem varDiag_rel {Γ} {t s : Tm Γ} :
    (varDiag : TrmRel).rel Γ t s ↔ ∃ x : Γ, t = Tm.var x ∧ s = Tm.var x :=
  Iff.rfl

@[simp] theorem scr_rel {φ : TrmRel} {Γ} {t s : Tm Γ} :
    (scr φ).rel Γ t s ↔
      (t = Tm.zero ∧ s = Tm.zero) ∨
      (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ φ.rel Γ t' s') ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                              φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                              φ.rel Γ m₁ m₂ ∧ φ.rel Γ n₁ n₂) := Iff.rfl

@[simp] theorem subst_rel {φ ψ : TrmRel} {Θ} {u v : Tm Θ} :
    (subst φ ψ).rel Θ u v ↔
      ∃ (Γ : Type) (t s : Tm Γ) (τ σ : Γ → Tm Θ),
        u = t.subst τ ∧ v = s.subst σ
        ∧ φ.rel Γ t s ∧ ∀ x, ψ.rel Θ (τ x) (σ x) := Iff.rfl

/-!
First pass — the axioms that discharge by unfolding definitions and
threading an existential through a constructor. No induction on `Tm`,
no appeal to choice, no gluing of contexts. Concretely: monotonicity of
`scr` and of `subst` in its right slot; commutation of `scr` and
`subst` with converse; join-preservation of `subst` in its left slot;
symmetry, co-transitivity, and disjointness of `varDiag` with the
compound layer `scr φ`.
-/

theorem scr_monotonicity {φ ψ : TrmRel} (h : φ ≤ ψ) : scr φ ≤ scr ψ := by
  intro Γ t s hs
  rcases hs with ⟨rfl, rfl⟩
              | ⟨t', s', rfl, rfl, hφ⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨t', s', rfl, rfl, h Γ t' s' hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                  h Γ m₁ m₂ hφm, h Γ n₁ n₂ hφn⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                  h Γ m₁ m₂ hφm, h Γ n₁ n₂ hφn⟩))

theorem subst_monotonicity_right {φ ψ ψ' : TrmRel} (h : ψ ≤ ψ') :
    subst φ ψ ≤ subst φ ψ' := by
  intro Θ u v hs
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩ := hs
  exact ⟨Γ, t, s, τ, σ, hu, hv, hφ, fun x => h Θ (τ x) (σ x) (hψ x)⟩

theorem scr_converse_commutation (φ : TrmRel) : scr (φᵒ) = (scr φ)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩
          | ⟨t', s', rfl, rfl, hφ⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨s', t', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))
  · rintro (⟨rfl, rfl⟩
          | ⟨t', s', rfl, rfl, hφ⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨s', t', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, hφm, hφn⟩))

theorem subst_converse_commutation (φ ψ : TrmRel) :
    (subst φ ψ)ᵒ = subst (φᵒ) (ψᵒ) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hv, hu, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hu, hv, hφ, fun x => hψ x⟩
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, s, t, σ, τ, hv, hu, hφ, fun x => hψ x⟩

theorem subst_join_preservation_left (𝒮 : Set TrmRel) (ψ : TrmRel) :
    subst (sSup 𝒮) ψ = sSup ((fun φ => subst φ ψ) '' 𝒮) := by
  ext Θ u v
  constructor
  · rintro ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩
    exact ⟨subst φ ψ, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, Γ, t, s, τ, σ, hu, hv, hφ, hψ⟩
    exact ⟨Γ, t, s, τ, σ, hu, hv, ⟨φ, hφ𝒮, hφ⟩, hψ⟩

theorem varDiag_symmetry : (varDiag : TrmRel)ᵒ ≤ varDiag := by
  intro Γ t s h
  obtain ⟨x, hs, ht⟩ := h
  exact ⟨x, ht, hs⟩

theorem varDiag_cotransitivity : (varDiag : TrmRel) ≤ varDiag * varDiag := by
  intro Γ t s h
  obtain ⟨x, ht, hs⟩ := h
  exact ⟨Tm.var x, ⟨x, ht, rfl⟩, ⟨x, rfl, hs⟩⟩

theorem varDiag_scr_orthogonality (φ : TrmRel) :
    (varDiag : TrmRel) * scr φ ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨x, _, rfl⟩, hscr⟩ := h
  rcases hscr with ⟨hu, _⟩
                | ⟨_, _, hu, _⟩
                | ⟨_, _, _, _, hu, _⟩
                | ⟨_, _, _, _, hu, _⟩ <;> cases hu

/-!
Second pass — proofs that need real work, though of a familiar kind.
`subst_varDiag_unit_right` extracts, via `Classical.axiomOfChoice`, a
common renaming from a pointwise-varDiag substitution. `subst_scr_oplaxity`
is a case-split over the four `scr`-cases. `scr_compositionality`
is a sixteen-case matrix: four constructor cases on each side, twelve
of which are shape-conflicts closed by `cases`, four of which are the
honest sub-proofs. `cr_fixpoint` and `cr_induction` together internalise
structural induction on `Tm` inside `TrmRel`, matching the abstract law
`Δ̂ ≤ φ ⇒ Δ ≤ φ` of Section 3.1.1 of the paper.
-/

theorem subst_varDiag_unit_left (ψ : TrmRel) : subst varDiag ψ = ψ := by
  ext Θ u v
  constructor
  · rintro ⟨_, _, _, τ, σ, rfl, rfl, ⟨x, rfl, rfl⟩, hψ⟩
    exact hψ x
  · intro hψ
    refine ⟨Unit, Tm.var (), Tm.var (), fun _ => u, fun _ => v,
            rfl, rfl, ⟨(), rfl, rfl⟩, ?_⟩
    intro _; exact hψ

theorem subst_varDiag_unit_right (φ : TrmRel) : subst φ varDiag = φ := by
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

theorem subst_scr_oplaxity (φ ψ : TrmRel) :
    subst (scr φ) ψ ≤ scr (subst φ ψ) := by
  intro Θ u v h
  obtain ⟨Γ, t, s, τ, σ, hu, hv, hscr, hψ⟩ := h
  rcases hscr with ⟨rfl, rfl⟩
                | ⟨t', s', rfl, rfl, hφ⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
  · exact Or.inl ⟨by rw [hu]; rfl, by rw [hv]; rfl⟩
  · refine Or.inr (Or.inl ⟨t'.subst τ, s'.subst σ,
                           by rw [hu]; rfl, by rw [hv]; rfl, ?_⟩)
    exact ⟨Γ, t', s', τ, σ, rfl, rfl, hφ, hψ⟩
  · refine Or.inr (Or.inr (Or.inl
      ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
       by rw [hu]; rfl, by rw [hv]; rfl, ?_, ?_⟩))
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, hφm, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hφn, hψ⟩
  · refine Or.inr (Or.inr (Or.inr
      ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
       by rw [hu]; rfl, by rw [hv]; rfl, ?_, ?_⟩))
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, hφm, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hφn, hψ⟩

theorem scr_compositionality (φ ψ : TrmRel) : scr (φ * ψ) = scr φ * scr ψ := by
  ext Γ t v
  constructor
  · rintro (⟨rfl, rfl⟩
          | ⟨t', v', rfl, rfl, ⟨u, hφ, hψ⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨u_m, hφm, hψm⟩, ⟨u_n, hφn, hψn⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨u_m, hφm, hψm⟩, ⟨u_n, hφn, hψn⟩⟩)
    · exact ⟨Tm.zero, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Tm.succ u, Or.inr (Or.inl ⟨t', u, rfl, rfl, hφ⟩),
                        Or.inr (Or.inl ⟨u, v', rfl, rfl, hψ⟩)⟩
    · exact ⟨Tm.plus u_m u_n,
             Or.inr (Or.inr (Or.inl ⟨m₁, u_m, n₁, u_n, rfl, rfl, hφm, hφn⟩)),
             Or.inr (Or.inr (Or.inl ⟨u_m, m₂, u_n, n₂, rfl, rfl, hψm, hψn⟩))⟩
    · exact ⟨Tm.mult u_m u_n,
             Or.inr (Or.inr (Or.inr ⟨m₁, u_m, n₁, u_n, rfl, rfl, hφm, hφn⟩)),
             Or.inr (Or.inr (Or.inr ⟨u_m, m₂, u_n, n₂, rfl, rfl, hψm, hψn⟩))⟩
  · rintro ⟨w, h1, h2⟩
    rcases h1 with ⟨rfl, hw⟩
                | ⟨t', w', rfl, rfl, hφ⟩
                | ⟨m₁, wm, n₁, wn, rfl, rfl, hφm, hφn⟩
                | ⟨m₁, wm, n₁, wn, rfl, rfl, hφm, hφn⟩
    · -- w = zero
      subst hw
      rcases h2 with ⟨_, rfl⟩
                  | ⟨_, _, hw, _⟩
                  | ⟨_, _, _, _, hw, _⟩
                  | ⟨_, _, _, _, hw, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · cases hw
      · cases hw
      · cases hw
    · rcases h2 with ⟨hw, _⟩
                  | ⟨w'', v', hw, rfl, hψ⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
      · cases hw
      · have : w' = w'' := Tm.succ.inj hw
        subst this
        exact Or.inr (Or.inl ⟨t', v', rfl, rfl, ⟨w', hφ, hψ⟩⟩)
      · cases hw
      · cases hw
    · rcases h2 with ⟨hw, _⟩
                  | ⟨_, _, hw, _⟩
                  | ⟨wm', m₂, wn', n₂, hw, rfl, hψm, hψn⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
      · cases hw
      · cases hw
      · obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp hw
        subst hm; subst hn
        exact Or.inr (Or.inr (Or.inl
          ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, hφm, hψm⟩, ⟨wn, hφn, hψn⟩⟩))
      · cases hw
    · rcases h2 with ⟨hw, _⟩
                  | ⟨_, _, hw, _⟩
                  | ⟨_, _, _, _, hw, _, _, _⟩
                  | ⟨wm', m₂, wn', n₂, hw, rfl, hψm, hψn⟩
      · cases hw
      · cases hw
      · cases hw
      · obtain ⟨hm, hn⟩ := Tm.mult.injEq _ _ _ _ |>.mp hw
        subst hm; subst hn
        exact Or.inr (Or.inr (Or.inr
          ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, hφm, hψm⟩, ⟨wn, hφn, hψn⟩⟩))

theorem cr_fixpoint : (varDiag ⊔ scr 1 : TrmRel) = 1 := by
  ext Γ t s
  constructor
  · intro h
    rcases h with ⟨x, rfl, rfl⟩
                | (⟨rfl, rfl⟩
                  | ⟨t', s', rfl, rfl, hφ⟩
                  | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
                  | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · rfl
    · rfl
    · exact congrArg Tm.succ hφ
    · exact congrArg₂ Tm.plus hφm hφn
    · exact congrArg₂ Tm.mult hφm hφn
  · intro (h : t = s)
    subst h
    cases t with
    | var x    => exact Or.inl ⟨x, rfl, rfl⟩
    | zero     => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | succ t'  => exact Or.inr (Or.inr (Or.inl ⟨t', t', rfl, rfl, rfl⟩))
    | plus m n => exact Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨m, m, n, n, rfl, rfl, rfl, rfl⟩)))
    | mult m n => exact Or.inr (Or.inr (Or.inr (Or.inr
                    ⟨m, m, n, n, rfl, rfl, rfl, rfl⟩)))

theorem cr_induction {φ : TrmRel}
    (h : varDiag ⊔ scr φ ≤ φ) : 1 ≤ φ := by
  intro Γ t s (heq : t = s)
  subst heq
  induction t with
  | var x =>
    exact h Γ (Tm.var x) (Tm.var x) (Or.inl ⟨x, rfl, rfl⟩)
  | zero =>
    exact h Γ Tm.zero Tm.zero (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | succ t' ih =>
    exact h Γ (Tm.succ t') (Tm.succ t')
      (Or.inr (Or.inr (Or.inl ⟨t', t', rfl, rfl, ih⟩)))
  | plus m n ihm ihn =>
    exact h Γ (Tm.plus m n) (Tm.plus m n)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, m, n, n, rfl, rfl, ihm, ihn⟩))))
  | mult m n ihm ihn =>
    exact h Γ (Tm.mult m n) (Tm.mult m n)
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, m, n, n, rfl, rfl, ihm, ihn⟩))))

/-!
Third pass — the two conceptually hard theorems. Associativity of
substitution states `subst (subst φ ψ) χ = subst φ (subst ψ χ)`, and
its ⇐-direction has to glue a Γ-indexed family of source contexts
`G : Γ → Type` into a single source context `Σ (x : Γ), G x` in order
to fit the shape of the LHS; this is the concrete face of the
"flatten a fibration" step of the categorical proof, and it is
unavoidable given the "contexts as types" decision. Oplax
compositionality states `subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ'`,
and its ⇒-direction uses `Classical.axiomOfChoice` to pick a *single*
intermediate substitution `μ` at each variable, closing the diagram
cleanly into the two halves of the target composition; the reverse
inequality fails in general, hence "oplax".
-/

theorem subst_associativity (φ ψ χ : TrmRel) :
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
    let τ₀ : Γ → Tm Γ' := fun x => (TT x).ren (inj x)
    let σ₀ : Γ → Tm Γ' := fun x => (SS x).ren (inj x)
    let τ₁ : Γ' → Tm Δ := fun p => TA p.1 p.2
    let σ₁ : Γ' → Tm Δ := fun p => SI p.1 p.2
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

theorem subst_compositionality_oplax (φ φ' ψ ψ' : TrmRel) :
    subst (φ * φ') (ψ * ψ') ≤ subst φ ψ * subst φ' ψ' := by
  intro Δ u v h
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, ⟨w, hφ, hφ'⟩, hpsi⟩ := h
  choose μ hψ hψ' using hpsi
  refine ⟨w.subst μ, ?_, ?_⟩
  · exact ⟨Γ, t, w, τ, μ, rfl, rfl, hφ, hψ⟩
  · exact ⟨Γ, w, s, μ, σ, rfl, rfl, hφ', hψ'⟩

/-!
The fourth TRA operation, `j`, distinguishes closed terms from open
ones inside the algebra: it relates `t` to `s` iff `t = s` and `t` is
the weakening of some `t₀ : ClosedTm`. As a `TrmRel` it is a
coreflexive (a subset of the diagonal), supported on the image of
`Tm.close`. The four axioms below — coreflexivity, symmetry,
cotransitivity, and orthogonality with `varDiag` — are all immediate
from the definition, with the last one using that a closed term cannot
be a variable.
-/

/-- The closure constant (paper: `□Δ`): relates `t` to itself provided
`t` is the weakening of some `t₀ : ClosedTm`. A coreflexive supported
on the image of `Tm.close Γ : ClosedTm → Tm Γ`; the abstract `TRA.box`
modality is built from it, and the four axioms below are the bare
minimum for `box` to behave as a monotone comonad. -/
def j : TrmRel := {
  rel := fun Γ t s => t = s ∧ ∃ t₀ : ClosedTm, t = Tm.close Γ t₀
  ren_closed := by
    intro Γ Δ f t s h
    obtain ⟨hts, t₀, ht⟩ := h
    refine ⟨by rw [hts], t₀, ?_⟩
    rw [ht, Tm.ren_close]
}

@[simp] theorem j_rel {Γ} {t s : Tm Γ} :
    (j : TrmRel).rel Γ t s ↔
      t = s ∧ ∃ t₀ : ClosedTm, t = Tm.close Γ t₀ := Iff.rfl

theorem j_coreflexivity : (j : TrmRel) ≤ 1 := fun _ _ _ h => h.1

theorem j_symmetry : (j : TrmRel)ᵒ ≤ j := by
  intro Γ t s h
  obtain ⟨hst, t₀, hs⟩ := h
  exact ⟨hst.symm, t₀, hst.symm.trans hs⟩

theorem j_cotransitivity : (j : TrmRel) ≤ j * j := by
  intro Γ t s h
  refine ⟨t, ⟨rfl, ?_⟩, h⟩
  obtain ⟨_, t₀, ht⟩ := h
  exact ⟨t₀, ht⟩

theorem j_varDiag_orthogonality : (j : TrmRel) * varDiag ≤ ⊥ := by
  intro Γ t v h
  obtain ⟨u, ⟨htu, t₀, hcls⟩, ⟨x, huvar, _⟩⟩ := h
  subst htu; subst huvar
  cases t₀ with
  | var y   => exact y.elim
  | zero    => cases hcls
  | succ _  => cases hcls
  | plus _ _ => cases hcls
  | mult _ _ => cases hcls

end TrmRel

/-!
The previous section did the work; here we simply collect it. The
`instance TRA TrmRel` declaration is a form-filling exercise: for each
of the twenty TRA fields we hand back the corresponding proof. Peano
has no binders, so the model proves `subst_scr_oplaxity` without the
class-level `Δη ≤ b` guard (the field is `fun a b _ =>
TrmRel.subst_scr_oplaxity a b`); at the second-order level the guard
does real work, see `LeanTra.Instances.Lambda.TRA`. From this point on, every
abstract lemma proved against a generic `TRA α` — including the
closure modality `TRA.box`, the combinator `TRA.cr`, and eventually
the bridge theorem itself — becomes a concrete lemma about `TrmRel`.
The two lemmas that close the section are sanity checks:
`scr_top_ne_bot` witnesses that `TrmRel` is non-degenerate, and
`substJClosed` verifies `TRA.IsClosed (subst a j)`, recorded here but
not consumed elsewhere.
-/

instance instTRA : TRA TrmRel where
  varDiag := TrmRel.varDiag
  scr := TrmRel.scr
  subst := TrmRel.subst
  varDiag_symmetry := TrmRel.varDiag_symmetry
  varDiag_cotransitivity := TrmRel.varDiag_cotransitivity
  scr_monotonicity := fun _ _ h => TrmRel.scr_monotonicity h
  scr_compositionality := TrmRel.scr_compositionality
  scr_converse_commutation := TrmRel.scr_converse_commutation
  varDiag_scr_orthogonality := TrmRel.varDiag_scr_orthogonality
  subst_monotonicity_right := fun _ _ _ h => TrmRel.subst_monotonicity_right h
  subst_compositionality_oplax := TrmRel.subst_compositionality_oplax
  subst_converse_commutation := TrmRel.subst_converse_commutation
  subst_join_preservation_left := TrmRel.subst_join_preservation_left
  subst_varDiag_unit_left := TrmRel.subst_varDiag_unit_left
  subst_varDiag_unit_right := TrmRel.subst_varDiag_unit_right
  subst_associativity := TrmRel.subst_associativity
  subst_scr_oplaxity := fun a b _ => TrmRel.subst_scr_oplaxity a b
  cr_fixpoint := TrmRel.cr_fixpoint
  cr_induction := fun _ h => TrmRel.cr_induction h
  j := TrmRel.j
  j_coreflexivity := TrmRel.j_coreflexivity
  j_symmetry := TrmRel.j_symmetry
  j_cotransitivity := TrmRel.j_cotransitivity
  j_varDiag_orthogonality := TrmRel.j_varDiag_orthogonality

namespace TrmRel

theorem scr_top_ne_bot : (scr ⊤ : TrmRel) ≠ ⊥ := by
  intro hbad
  have h : (scr ⊤ : TrmRel).rel Unit (Tm.succ (Tm.var ())) (Tm.succ (Tm.var ())) :=
    Or.inr (Or.inl ⟨Tm.var (), Tm.var (), rfl, rfl, trivial⟩)
  rw [hbad] at h; exact h

/-- Model-side verification of `TRA.IsClosed (subst a j)`. -/
theorem substJClosed (a : TrmRel) : TRA.IsClosed (TrmRel.subst a j) := by
  change TrmRel.subst a j ≤ TRA.box (TrmRel.subst a j)
  intro Θ u v hsubst
  have hsub := hsubst
  obtain ⟨Γ, t, s, τ, σ, rfl, rfl, _, hj⟩ := hsub
  have hτσ : ∀ x, τ x = σ x := fun x => (hj x).1
  have hτ_cls : ∀ x, ∃ t₀ : ClosedTm, τ x = Tm.close Θ t₀ :=
    fun x => (hj x).2
  obtain ⟨τ', hτ'eq⟩ := Classical.axiomOfChoice hτ_cls
  have hu_cls : (t.subst τ : Tm Θ) = Tm.close Θ (t.subst τ') := by
    change t.subst τ = (t.subst τ').ren Empty.elim
    rw [Tm.ren_subst]
    congr 1
    funext x
    exact hτ'eq x
  have hv_cls : (s.subst σ : Tm Θ) = Tm.close Θ (s.subst τ') := by
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

end TrmRel


end LeanTra.Instances.PeanoArithmetic
