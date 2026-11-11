/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Instances.Lambda.TRA
public import LeanTra.TRA.OperationalDecomposition

/-!
# Operational decomposition for the λ-calculus

The structural refinement `scr` on `TrmRel` splits into an introduction/elimination pair and
packages into an `OperationalDecomposition` instance.

## Main statements
* `TrmRel.scr_decomposition`: `scr a = introduction a ⊔ elimination a a`.
* `TrmRel.subst_introduction_oplaxity`, `TrmRel.subst_elimination_oplaxity`,
  `TrmRel.box_elimination_oplaxity`: the substitution/box oplaxity laws for the split.
* `TrmRel.instOperationalDecomposition`: the `OperationalDecomposition TrmRel` instance.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale TRA

namespace LeanTra.Instances.Lambda
namespace TrmRel

/-! ## Section 4: Operational decomposition and β-reduction

Once the TRA instance is in place, we specialise the machinery of
`TRA/OperationalDecomposition.lean` by splitting the structural
refinement `scr` into an *introduction* component (the `lam`-clause,
carrying constructors) and an *elimination* component (the `app`-clause,
carrying destructors). The two operations themselves are already
defined in Section 3, alongside the `subst_scr_oplaxity` block whose
docstring covers both sides of the story; what happens here is that
the split is turned into an `OperationalDecomposition` typeclass
instance, which is precisely what allows the Gentzen principles of
`Metatheory/GentzenPrinciples.lean` to be stated at all: those
principles talk about how a rewrite rule interacts with introduction
and elimination forms, and they can be formulated only on a syntax
that has been decomposed in this way. All fourteen accompanying
axioms are direct computations; the `subst_introduction_oplaxity`
one carries the same `Δη ≤ b` guard as `subst_scr_oplaxity` in
Section 3 and for the same reason. With the instance in hand the
section then introduces β-reduction as a `TrmRel`, verifies the five
rule-level local hypotheses required by the bridge theorem, and
finally cashes them into confluence of parallel β via
`LeanTra.Confluence.local_confluence`. -/

/-- `scr = introduction ⊔ elimination` on the diagonal. -/
theorem scr_decomposition (a : TrmRel) :
  (TRA.scr a : TrmRel) = introduction a ⊔ elimination a a := by
  ext n t s
  change (scr a).rel n t s ↔
    (introduction a).rel n t s ∨ (elimination a a).rel n t s
  simp only [scr_rel, introduction_rel, elimination_rel]

/-! ### OperationalDecomposition axioms

The fourteen axioms of the `OperationalDecomposition` class. They
mirror the shape of the corresponding `scr` laws from Section 3, but
split slot by slot into a constructor part (`introduction`, which
only sees the `lam` clause) and a destructor part (`elimination`,
which only sees the `app` clause). Monotonicity, join preservation,
compositionality, and the various converse-commutations reappear in
the two-slot form; the key new axiom is `scr_decomposition`, which
records that `scr` really is the join of introduction and
elimination on the diagonal. All fourteen close by direct term-level
computation; `subst_introduction_oplaxity` carries the same
`Δη ≤ b` guard as `subst_scr_oplaxity` in Section 3, for the same
binder-side reason. -/

/-- OD axiom: `introduction` preserves arbitrary joins. -/
theorem introduction_join_preservation (𝒮 : Set TrmRel) :
  introduction (sSup 𝒮) = sSup (introduction '' 𝒮) := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩
    exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, t', s', rfl, rfl, hφ⟩
    exact ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩

/-- OD axiom: `introduction` preserves composition. -/
theorem introduction_compositionality (a b : TrmRel) :
    introduction (a * b) = introduction a * introduction b := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t', v', rfl, rfl, u', ha, hb⟩
    exact ⟨Lam.lam u', ⟨t', u', rfl, rfl, ha⟩, ⟨u', v', rfl, rfl, hb⟩⟩
  · rintro ⟨u, ⟨t', u₁, rfl, hu, ha⟩, ⟨u₂, v', hu', rfl, hb⟩⟩
    have hu12 : u₁ = u₂ := Lam.lam.inj (hu.symm.trans hu')
    refine ⟨t', v', rfl, rfl, u₁, ha, ?_⟩
    rw [hu12]; exact hb

/-- OD axiom: `introduction` commutes with converse. -/
theorem introduction_converse_commutation (a : TrmRel) :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩
  · rintro ⟨t', s', rfl, rfl, ha⟩; exact ⟨s', t', rfl, rfl, ha⟩

/-- OD axiom: `elimination` preserves joins in its major (left) slot. -/
theorem elimination_join_preservation_left (𝒮 : Set TrmRel) (b : TrmRel) :
    elimination (sSup 𝒮) b = sSup ((fun a => elimination a b) '' 𝒮) := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨a, ha𝒮, ha⟩, hb⟩
    exact ⟨elimination a b, ⟨a, ha𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
  · rintro ⟨_, ⟨a, ha𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
    exact ⟨t₁, t₂, v₁, v₂, rfl, rfl, ⟨a, ha𝒮, ha⟩, hb⟩

/-- OD axiom: `elimination` preserves joins in its minor (right) slot. -/
theorem elimination_join_preservation_right (a : TrmRel) (𝒮 : Set TrmRel) :
    elimination a (sSup 𝒮) = sSup ((fun b => elimination a b) '' 𝒮) := by
  ext n t v
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, v₁, v₂, rfl, rfl, ha, ⟨b, hb𝒮, hb⟩⟩
    exact ⟨elimination a b, ⟨b, hb𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
  · rintro ⟨_, ⟨b, hb𝒮, rfl⟩, t₁, t₂, v₁, v₂, rfl, rfl, ha, hb⟩
    exact ⟨t₁, t₂, v₁, v₂, rfl, rfl, ha, ⟨b, hb𝒮, hb⟩⟩

/-- OD axiom: `elimination` preserves composition slot-by-slot. -/
theorem elimination_compositionality (a₁ a₂ b₁ b₂ : TrmRel) :
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

/-- OD axiom: `elimination` commutes with converse in both slots. -/
theorem elimination_converse_commutation (a b : TrmRel) :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext n t s
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩
  · rintro ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩
    exact ⟨s₁, s₂, t₁, t₂, rfl, rfl, ha, hb⟩

/-- OD axiom: `introduction 1 ≤ 1`, the introduction of equal bodies is
equality. -/
theorem introduction_unit_oplaxity : (introduction 1 : TrmRel) ≤ 1 := by
  rintro n t s ⟨t', s', rfl, rfl, (heq : t' = s')⟩
  exact congrArg Lam.lam heq

/-- OD axiom: `elimination 1 1 ≤ 1`, the application of equals to equals
is equality. -/
theorem elimination_unit_oplaxity : (elimination 1 1 : TrmRel) ≤ 1 := by
  rintro n t s ⟨t₁, t₂, s₁, s₂, rfl, rfl, (h₁ : t₁ = s₁), (h₂ : t₂ = s₂)⟩
  exact congrArg₂ Lam.app h₁ h₂

/-- OD axiom: introductions and eliminations are orthogonal,
`introduction a * elimination b c ≤ ⊥`. -/
theorem introduction_elimination_orthogonality (a b c : TrmRel) :
    introduction a * elimination b c ≤ ⊥ := by
  rintro n t v ⟨u, ⟨t', u', rfl, hu, _⟩,
                ⟨_, _, _, _, hu', _, _, _⟩⟩
  exact absurd (hu.symm.trans hu') (by intro h; cases h)

/-- `OperationalDecomposition.subst_introduction_oplaxity` in this
model: with the guard `Δη ≤ b`, substituting into an introduction
form refines an introduction. Same structural argument as
`subst_scr_oplaxity`, restricted to the `lam` clause; the guard is
required for the same binder-side reason. -/
theorem subst_introduction_oplaxity (a b : TrmRel) (hvar : varDiag ≤ b) :
    subst (introduction a) b ≤ introduction (subst a b) := by
  rintro m u v ⟨n, u₀, v₀, τ, σ, rfl, rfl, ⟨t', s', rfl, rfl, ha⟩, hψ⟩
  refine ⟨t'.subst (Lam.liftSubst τ), s'.subst (Lam.liftSubst σ), rfl, rfl, ?_⟩
  exact ⟨n + 1, t', s', Lam.liftSubst τ, Lam.liftSubst σ,
         rfl, rfl, ha,
         subst_liftSubst_ren_succ_of_le b τ σ hψ hvar⟩

/-- OD axiom: oplaxness of `subst` on the `elimination` slot. -/
theorem subst_elimination_oplaxity (a₁ a₂ b : TrmRel) :
    subst (elimination a₁ a₂) b ≤ elimination (subst a₁ b) (subst a₂ b) := by
  rintro m u v ⟨n, t, s, τ, σ, rfl, rfl, ⟨t₁, t₂, s₁, s₂, rfl, rfl, ha, hb⟩, hψ⟩
  refine ⟨t₁.subst τ, t₂.subst τ, s₁.subst σ, s₂.subst σ,
          rfl, rfl, ?_, ?_⟩
  · exact ⟨n, t₁, s₁, τ, σ, rfl, rfl, ha, hψ⟩
  · exact ⟨n, t₂, s₂, τ, σ, rfl, rfl, hb, hψ⟩

theorem box_elimination_oplaxity (a b : TrmRel) :
    (TRA.box (elimination a b) : TrmRel) ≤ elimination (TRA.box a) b := by
  -- Unfold box = j * · * j = (j * ·) * j. Peel off both `j`s (which force
  -- closedness at the endpoints) then case-analyse the closed source and
  -- target to invert the outer `app` and rebuild `elimination (box a) b`.
  intro n u v h
  -- h : ((j * elimination a b) * j).rel n u v
  obtain ⟨w, hjeab, hjwv⟩ := h
  -- hjeab : (j * elimination a b).rel n u w
  obtain ⟨w', hju, hab⟩ := hjeab
  -- hju : j.rel n u w'  ⇒  u = w' ∧ ∃ u₀, u = close n u₀
  obtain ⟨huw', u₀, hu_close⟩ := hju
  subst huw'
  -- hab : (elimination a b).rel n u w
  obtain ⟨t₁, t₂, s₁, s₂, hu_eq, hw_eq, ha, hb⟩ := hab
  -- hjwv : j.rel n w v  ⇒  w = v ∧ ∃ v₀, w = close n v₀
  obtain ⟨hwv, v₀, hv_close⟩ := hjwv
  subst hwv
  -- Invert close on u₀ to expose the app shape.
  cases u₀ with
  | var x =>
    exfalso
    have : Lam.close n (Lam.var x) = Lam.app t₁ t₂ := hu_close.symm.trans hu_eq
    cases this
  | lam _ =>
    exfalso
    have : Lam.close n (Lam.lam _) = Lam.app t₁ t₂ := hu_close.symm.trans hu_eq
    cases this
  | app u₀₁ u₀₂ =>
    have huc : Lam.app (Lam.close n u₀₁) (Lam.close n u₀₂) = Lam.app t₁ t₂ :=
      hu_close.symm.trans hu_eq
    obtain ⟨ht₁_eq, ht₂_eq⟩ := (Lam.app.injEq _ _ _ _).mp huc
    cases v₀ with
    | var x =>
      exfalso
      have : Lam.close n (Lam.var x) = Lam.app s₁ s₂ := hv_close.symm.trans hw_eq
      cases this
    | lam _ =>
      exfalso
      have : Lam.close n (Lam.lam _) = Lam.app s₁ s₂ := hv_close.symm.trans hw_eq
      cases this
    | app v₀₁ v₀₂ =>
      have hwc : Lam.app (Lam.close n v₀₁) (Lam.close n v₀₂) = Lam.app s₁ s₂ :=
        hv_close.symm.trans hw_eq
      obtain ⟨hs₁_eq, hs₂_eq⟩ := (Lam.app.injEq _ _ _ _).mp hwc
      refine ⟨t₁, t₂, s₁, s₂, hu_eq, hw_eq, ?_, hb⟩
      -- Goal: (TRA.box a).rel n t₁ s₁ = ((j * a) * j).rel n t₁ s₁
      -- Middle witness s₁: (j * a).rel n t₁ s₁ ∧ j.rel n s₁ s₁.
      refine ⟨s₁, ⟨t₁, ⟨rfl, u₀₁, ht₁_eq.symm⟩, ha⟩,
                    ⟨rfl, v₀₁, hs₁_eq.symm⟩⟩

/-! ### OperationalDecomposition instance

The counterpart of `instTRA` for the operational-decomposition layer:
the fourteen axioms above are bundled into
`instOperationalDecomposition : OperationalDecomposition TrmRel`, so
that every abstract lemma stated over the class becomes applicable to
`TrmRel`. In particular this is what makes the Gentzen principles
`GIP` and `GCP` of `Metatheory/GentzenPrinciples.lean` statable on
`betaRule` in the next sub-section: those principles are defined only
for carriers that carry an `OperationalDecomposition`, and would be
inexpressible without it. -/

/-- The syntax relations on λ-terms carry an `OperationalDecomposition`
structure, splitting `scr` into `introduction` (the `lam` clause) and
`elimination` (the `app` clause). -/
instance instOperationalDecomposition : OperationalDecomposition TrmRel where
  introduction := introduction
  elimination := elimination
  introduction_join_preservation s _ := introduction_join_preservation s
  introduction_compositionality := introduction_compositionality
  introduction_converse_commutation := introduction_converse_commutation
  elimination_join_preservation_left s _ b := elimination_join_preservation_left s b
  elimination_join_preservation_right a s _ := elimination_join_preservation_right a s
  elimination_compositionality := elimination_compositionality
  elimination_converse_commutation := elimination_converse_commutation
  introduction_unit_oplaxity := introduction_unit_oplaxity
  elimination_unit_oplaxity := elimination_unit_oplaxity
  introduction_elimination_orthogonality := introduction_elimination_orthogonality
  scr_decomposition := scr_decomposition
  subst_introduction_oplaxity := subst_introduction_oplaxity
  subst_elimination_oplaxity := subst_elimination_oplaxity
  box_elimination_oplaxity := box_elimination_oplaxity

end TrmRel
end LeanTra.Instances.Lambda
