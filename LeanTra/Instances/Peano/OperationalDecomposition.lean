/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Instances.Peano.TRA
public import LeanTra.TRA.OperationalDecomposition

/-!
# Operational decomposition for Peano arithmetic

The structural refinement `scr` on `TrmRel` splits into an introduction/elimination pair and
packages into an `OperationalDecomposition` instance.

## Main definitions
* `TrmRel.introduction`, `TrmRel.elimination`: the constructor and destructor slices of `scr`.

## Main statements
* `instOperationalDecomposition`: the `OperationalDecomposition TrmRel` instance.

## Implementation notes

`introduction_join_preservation` requires `𝒮.Nonempty`: the nullary constructor `zero`
makes `introduction ⊥` relate `(zero, zero)` regardless of its argument, so without the
non-empty-set hypothesis `introduction ⊥ ≠ ⊥`. The paper only requires ω-cocontinuity
(Def. 6, p. 11) and every internal consumer of the axiom applies it to non-empty joins,
so the relaxation is faithful to the paper.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.PeanoArithmetic

/-!
`TrmRel` is now a full-blown `TRA`. The next layer refines the strict
compatible refinement `scr` into its constructor slice `introduction`
and its destructor slice `elimination`, matching the paper's cocartesian
decomposition of `~·`. In our signature `introduction a` covers the two
constructor cases `(zero, zero)` and `(succ t', succ s')` — the first
carrying no premise on `a`, since `zero` is nullary — while
`elimination a b` covers the two destructor cases `(plus m₁ n₁, plus m₂ n₂)`
and `(mult m₁ n₁, mult m₂ n₂)`, with `a` on the major slot and `b` on
the minor. The fourteen axioms of `OperationalDecomposition` — join
preservation, compositionality and converse for each operation, oplax
unit laws, orthogonality of intro and elim, the decomposition
`scr a = introduction a ⊔ elimination a a`, and the three oplax laws
governing substitution and the closure modality — are then discharged
one at a time by the same kind of case-splitting that dominated
Section 3. The heaviest single proof is `box_elimination_oplaxity`,
which case-splits on all five `Tm` constructors for each of the two
closed-term slots. `introduction_join_preservation` carries the
`𝒮.Nonempty` hypothesis, the relaxation discussed in the module
preamble; without it the nullary `zero`-case would be inconsistent with
the empty-set instance of the axiom.
-/

namespace TrmRel

/-- The constructor slice of `scr`. Two cases: `(zero, zero)` — nullary
intro form, no `a`-premise, and the case that forces the non-empty-join
relaxation of the framework axiom — and `(succ t', succ s')` with
`a t' s'`. No `plus` or `mult`; those live in `elimination` below, and
the two operations are orthogonal by construction. -/
def introduction (a : TrmRel) : TrmRel := {
  rel := fun Γ t s =>
    (t = Tm.zero ∧ s = Tm.zero) ∨
    (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ a.rel Γ t' s')
  ren_closed := by
    intro _ _ f _ _ h
    rcases h with ⟨rfl, rfl⟩ | ⟨t', s', ht, hs, ha⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨t'.ren f, s'.ren f, by rw [ht]; rfl, by rw [hs]; rfl,
                    a.ren_closed f ha⟩
}

/-- The destructor slice of `scr`. Two cases: `(plus m₁ n₁, plus m₂ n₂)`
with `a m₁ m₂` (major) and `b n₁ n₂` (minor), and
`(mult m₁ n₁, mult m₂ n₂)` with the same slot convention. Slot 0 is
major throughout, which is what makes the Gentzen principles below
speak of the left argument of `plus` and `mult` as the evaluated one. -/
def elimination (a b : TrmRel) : TrmRel := {
  rel := fun Γ t s =>
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                            a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂) ∨
    (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                            a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂)
  ren_closed := by
    intro _ _ f _ _ h
    rcases h with ⟨m₁, m₂, n₁, n₂, ht, hs, ha, hb⟩
                | ⟨m₁, m₂, n₁, n₂, ht, hs, ha, hb⟩
    · exact Or.inl ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    by rw [ht]; rfl, by rw [hs]; rfl,
                    a.ren_closed f ha, b.ren_closed f hb⟩
    · exact Or.inr ⟨m₁.ren f, m₂.ren f, n₁.ren f, n₂.ren f,
                    by rw [ht]; rfl, by rw [hs]; rfl,
                    a.ren_closed f ha, b.ren_closed f hb⟩
}

@[simp] theorem introduction_rel {a : TrmRel} {Γ} {t s : Tm Γ} :
    (introduction a).rel Γ t s ↔
      (t = Tm.zero ∧ s = Tm.zero) ∨
      (∃ t' s' : Tm Γ, t = Tm.succ t' ∧ s = Tm.succ s' ∧ a.rel Γ t' s') :=
  Iff.rfl

@[simp] theorem elimination_rel {a b : TrmRel} {Γ} {t s : Tm Γ} :
    (elimination a b).rel Γ t s ↔
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.plus m₁ n₁ ∧ s = Tm.plus m₂ n₂ ∧
                              a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂) ∨
      (∃ m₁ m₂ n₁ n₂ : Tm Γ, t = Tm.mult m₁ n₁ ∧ s = Tm.mult m₂ n₂ ∧
                              a.rel Γ m₁ m₂ ∧ b.rel Γ n₁ n₂) := Iff.rfl

/-!
The three semirelator axioms for each of `introduction` and
`elimination`: join preservation, compositionality, and converse
commutation. Nine theorems in total; the pattern is uniform, differing
only in which constructor case is being propagated through which
operation.
-/

theorem introduction_join_preservation (𝒮 : Set TrmRel) (h𝒮 : 𝒮.Nonempty) :
    introduction (sSup 𝒮) = sSup (introduction '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩)
    · -- zero case: pick any witness in 𝒮 to place the derivation.
      obtain ⟨φ, hφ𝒮⟩ := h𝒮
      exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨introduction φ, ⟨φ, hφ𝒮, rfl⟩, Or.inr ⟨t', s', rfl, rfl, hφ⟩⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, hφ⟩
    rcases hφ with ⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, hφ⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨t', s', rfl, rfl, φ, hφ𝒮, hφ⟩

theorem introduction_compositionality (a b : TrmRel) :
    introduction (a * b) = introduction a * introduction b := by
  ext Γ t v
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨t', v', rfl, rfl, u', ha, hb⟩)
    · exact ⟨Tm.zero, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Tm.succ u',
             Or.inr ⟨t', u', rfl, rfl, ha⟩,
             Or.inr ⟨u', v', rfl, rfl, hb⟩⟩
  · rintro ⟨u, h1, h2⟩
    rcases h1 with ⟨rfl, hu⟩ | ⟨t', u₁, rfl, hu, ha⟩
    · -- u = zero
      subst hu
      rcases h2 with ⟨_, rfl⟩ | ⟨_, _, hu, _, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · cases hu
    · rcases h2 with ⟨hu', _⟩ | ⟨u₂, v', hu', rfl, hb⟩
      · cases hu.symm.trans hu'
      · have hu12 : u₁ = u₂ := Tm.succ.inj (hu.symm.trans hu')
        refine Or.inr ⟨t', v', rfl, rfl, u₁, ha, ?_⟩
        rw [hu12]; exact hb

theorem introduction_converse_commutation (a : TrmRel) :
    introduction (aᵒ) = (introduction a)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, ha⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨s', t', rfl, rfl, ha⟩
  · rintro (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, ha⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨s', t', rfl, rfl, ha⟩

theorem elimination_join_preservation_left (𝒮 : Set TrmRel) (b : TrmRel) :
    elimination (sSup 𝒮) b = sSup ((fun a => elimination a b) '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩)
    · exact ⟨elimination φ b, ⟨φ, hφ𝒮, rfl⟩,
             Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩⟩
    · exact ⟨elimination φ b, ⟨φ, hφ𝒮, rfl⟩,
             Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, h⟩
    rcases h with ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφ, hb⟩
    · exact Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩
    · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨φ, hφ𝒮, hφ⟩, hb⟩

theorem elimination_join_preservation_right (a : TrmRel) (𝒮 : Set TrmRel) :
    elimination a (sSup 𝒮) = sSup ((fun b => elimination a b) '' 𝒮) := by
  ext Γ t s
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩)
    · exact ⟨elimination a φ, ⟨φ, hφ𝒮, rfl⟩,
             Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩⟩
    · exact ⟨elimination a φ, ⟨φ, hφ𝒮, rfl⟩,
             Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩⟩
  · rintro ⟨_, ⟨φ, hφ𝒮, rfl⟩, h⟩
    rcases h with ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hφ⟩
    · exact Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩
    · exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, ⟨φ, hφ𝒮, hφ⟩⟩

theorem elimination_compositionality (a₁ a₂ b₁ b₂ : TrmRel) :
    elimination (a₁ * a₂) (b₁ * b₂) = elimination a₁ b₁ * elimination a₂ b₂ := by
  ext Γ t v
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, ha₁, ha₂⟩, ⟨wn, hb₁, hb₂⟩⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ⟨wm, ha₁, ha₂⟩, ⟨wn, hb₁, hb₂⟩⟩)
    · exact ⟨Tm.plus wm wn,
             Or.inl ⟨m₁, wm, n₁, wn, rfl, rfl, ha₁, hb₁⟩,
             Or.inl ⟨wm, m₂, wn, n₂, rfl, rfl, ha₂, hb₂⟩⟩
    · exact ⟨Tm.mult wm wn,
             Or.inr ⟨m₁, wm, n₁, wn, rfl, rfl, ha₁, hb₁⟩,
             Or.inr ⟨wm, m₂, wn, n₂, rfl, rfl, ha₂, hb₂⟩⟩
  · rintro ⟨u, h1, h2⟩
    rcases h1 with ⟨m₁, um, n₁, un, rfl, hu, ha₁, hb₁⟩
                | ⟨m₁, um, n₁, un, rfl, hu, ha₁, hb₁⟩
    · rcases h2 with ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
                  | ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
      · have heq : Tm.plus um un = Tm.plus um' un' := hu.symm.trans hu'
        obtain ⟨hm, hn⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
        subst hm; subst hn
        exact Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                      ⟨um, ha₁, ha₂⟩, ⟨un, hb₁, hb₂⟩⟩
      · cases hu.symm.trans hu'
    · rcases h2 with ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
                  | ⟨um', m₂, un', n₂, hu', rfl, ha₂, hb₂⟩
      · cases hu.symm.trans hu'
      · have heq : Tm.mult um un = Tm.mult um' un' := hu.symm.trans hu'
        obtain ⟨hm, hn⟩ := Tm.mult.injEq _ _ _ _ |>.mp heq
        subst hm; subst hn
        exact Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl,
                      ⟨um, ha₁, ha₂⟩, ⟨un, hb₁, hb₂⟩⟩

theorem elimination_converse_commutation (a b : TrmRel) :
    elimination (aᵒ) (bᵒ) = (elimination a b)ᵒ := by
  ext Γ t s
  constructor
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩)
    · exact Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
    · exact Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
  · rintro (⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩)
    · exact Or.inl ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩
    · exact Or.inr ⟨m₂, m₁, n₂, n₁, rfl, rfl, ha, hb⟩

/-!
Oplax unit laws for both operations, orthogonality (a constructor
composed with a destructor is `⊥`), and the decomposition equality
`scr a = introduction a ⊔ elimination a a` that certifies our two
slices really do add up to the strict compatible refinement.
-/

theorem introduction_unit_oplaxity : (introduction 1 : TrmRel) ≤ 1 := by
  rintro Γ t s (⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, (heq : t' = s')⟩)
  · rfl
  · exact congrArg Tm.succ heq

theorem elimination_unit_oplaxity : (elimination 1 1 : TrmRel) ≤ 1 := by
  rintro Γ t s (⟨m₁, m₂, n₁, n₂, rfl, rfl, (hm : m₁ = m₂), (hn : n₁ = n₂)⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, (hm : m₁ = m₂), (hn : n₁ = n₂)⟩)
  · exact congrArg₂ Tm.plus hm hn
  · exact congrArg₂ Tm.mult hm hn

theorem introduction_elimination_orthogonality (a b c : TrmRel) :
    introduction a * elimination b c ≤ ⊥ := by
  rintro Γ t v ⟨u, h1, h2⟩
  rcases h1 with ⟨rfl, hu⟩ | ⟨t', u', rfl, hu, _⟩
  · -- u = zero
    subst hu
    rcases h2 with ⟨_, _, _, _, hu, _, _, _⟩ | ⟨_, _, _, _, hu, _, _, _⟩ <;> cases hu
  · rcases h2 with ⟨_, _, _, _, hu', _, _, _⟩ | ⟨_, _, _, _, hu', _, _, _⟩ <;>
      exact absurd (hu.symm.trans hu') (by intro h; cases h)

theorem scr_decomposition (a : TrmRel) :
    (TRA.scr a : TrmRel) = introduction a ⊔ elimination a a := by
  ext Γ t s
  constructor
  · rintro (⟨rfl, rfl⟩
          | ⟨t', s', rfl, rfl, hφ⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
          | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨t', s', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
    · exact Or.inr (Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩)
  · rintro ((⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, hφ⟩)
          | (⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩
              | ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩))
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨t', s', rfl, rfl, hφ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m₁, m₂, n₁, n₂, rfl, rfl, hφm, hφn⟩))

/-!
The three oplax laws relating the intro / elim decomposition to
substitution and to the closure modality `TRA.box`.
`box_elimination_oplaxity` is the technically heaviest theorem of the
section: it requires a full five-way case-split on the closed term
underlying the elimination form's major argument.
-/

theorem subst_introduction_oplaxity (a b : TrmRel) :
    subst (introduction a) b ≤ introduction (subst a b) := by
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, hintro, hψ⟩
  rcases hintro with ⟨rfl, rfl⟩ | ⟨t', s', rfl, rfl, ha⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨t'.subst τ, s'.subst σ, rfl, rfl, ?_⟩
    exact ⟨Γ, t', s', τ, σ, rfl, rfl, ha, hψ⟩

theorem subst_elimination_oplaxity (a b c : TrmRel) :
    subst (elimination a b) c ≤ elimination (subst a c) (subst b c) := by
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, helim, hψ⟩
  rcases helim with ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
                | ⟨m₁, m₂, n₁, n₂, rfl, rfl, ha, hb⟩
  · refine Or.inl ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
                   rfl, rfl, ?_, ?_⟩
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, ha, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hb, hψ⟩
  · refine Or.inr ⟨m₁.subst τ, m₂.subst σ, n₁.subst τ, n₂.subst σ,
                   rfl, rfl, ?_, ?_⟩
    · exact ⟨Γ, m₁, m₂, τ, σ, rfl, rfl, ha, hψ⟩
    · exact ⟨Γ, n₁, n₂, τ, σ, rfl, rfl, hb, hψ⟩

theorem box_elimination_oplaxity (a b : TrmRel) :
    (TRA.box (elimination a b) : TrmRel) ≤ elimination (TRA.box a) b := by
  intro Θ u v h
  obtain ⟨w, hjeab, hjwv⟩ := h
  obtain ⟨w', hju, hab⟩ := hjeab
  obtain ⟨huw', u₀, hu_close⟩ := hju
  subst huw'
  obtain ⟨hwv, v₀, hv_close⟩ := hjwv
  subst hwv
  rcases hab with ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, hab_maj, hab_min⟩
                | ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, hab_maj, hab_min⟩
  · -- plus branch: `close Θ u₀ = plus m₁ n₁`
    cases u₀ with
    | var x => exact x.elim
    | zero =>
      have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | succ _ =>
      have : Tm.close Θ (Tm.succ _) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | plus u₀m u₀n =>
      have hu_shape :
          Tm.plus (Tm.close Θ u₀m) (Tm.close Θ u₀n) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      obtain ⟨hm_eq, hn_eq⟩ := Tm.plus.injEq _ _ _ _ |>.mp hu_shape
      cases v₀ with
      | var x => exact x.elim
      | zero =>
        have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | succ _ =>
        have : Tm.close Θ (Tm.succ _) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | plus v₀m v₀n =>
        have hv_shape :
            Tm.plus (Tm.close Θ v₀m) (Tm.close Θ v₀n) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        obtain ⟨hm_eq', hn_eq'⟩ := Tm.plus.injEq _ _ _ _ |>.mp hv_shape
        refine Or.inl ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, ?_, hab_min⟩
        refine ⟨m₂, ⟨m₁, ⟨rfl, u₀m, hm_eq.symm⟩, hab_maj⟩,
                ⟨rfl, v₀m, hm_eq'.symm⟩⟩
      | mult v₀m v₀n =>
        have : Tm.close Θ (Tm.mult _ _) = Tm.plus m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
    | mult _ _ =>
      have : Tm.close Θ (Tm.mult _ _) = Tm.plus m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
  · -- mult branch: `close Θ u₀ = mult m₁ n₁`
    cases u₀ with
    | var x => exact x.elim
    | zero =>
      have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | succ _ =>
      have : Tm.close Θ (Tm.succ _) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | plus _ _ =>
      have : Tm.close Θ (Tm.plus _ _) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      cases this
    | mult u₀m u₀n =>
      have hu_shape :
          Tm.mult (Tm.close Θ u₀m) (Tm.close Θ u₀n) = Tm.mult m₁ n₁ :=
        hu_close.symm.trans hu_eq
      obtain ⟨hm_eq, hn_eq⟩ := Tm.mult.injEq _ _ _ _ |>.mp hu_shape
      cases v₀ with
      | var x => exact x.elim
      | zero =>
        have : (Tm.close Θ Tm.zero : Tm Θ) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | succ _ =>
        have : Tm.close Θ (Tm.succ _) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | plus _ _ =>
        have : Tm.close Θ (Tm.plus _ _) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        cases this
      | mult v₀m v₀n =>
        have hv_shape :
            Tm.mult (Tm.close Θ v₀m) (Tm.close Θ v₀n) = Tm.mult m₂ n₂ :=
          hv_close.symm.trans hw_eq
        obtain ⟨hm_eq', hn_eq'⟩ := Tm.mult.injEq _ _ _ _ |>.mp hv_shape
        refine Or.inr ⟨m₁, m₂, n₁, n₂, hu_eq, hw_eq, ?_, hab_min⟩
        refine ⟨m₂, ⟨m₁, ⟨rfl, u₀m, hm_eq.symm⟩, hab_maj⟩,
                ⟨rfl, v₀m, hm_eq'.symm⟩⟩

end TrmRel

/-!
Assembly of the fourteen theorems above into the
`OperationalDecomposition TrmRel` instance. The two join-preservation
fields require passing the `𝒮.Nonempty` proof through the wrapper
lambda; the other twelve are direct.
-/

instance instOperationalDecomposition : OperationalDecomposition TrmRel where
  introduction := TrmRel.introduction
  elimination := TrmRel.elimination
  introduction_join_preservation 𝒮 h𝒮 :=
    TrmRel.introduction_join_preservation 𝒮 h𝒮
  elimination_join_preservation_left := fun 𝒮 _ b =>
    TrmRel.elimination_join_preservation_left 𝒮 b
  elimination_join_preservation_right := fun a 𝒮 _ =>
    TrmRel.elimination_join_preservation_right a 𝒮
  introduction_compositionality := TrmRel.introduction_compositionality
  introduction_converse_commutation := TrmRel.introduction_converse_commutation
  elimination_compositionality := TrmRel.elimination_compositionality
  elimination_converse_commutation := TrmRel.elimination_converse_commutation
  introduction_unit_oplaxity := TrmRel.introduction_unit_oplaxity
  elimination_unit_oplaxity := TrmRel.elimination_unit_oplaxity
  introduction_elimination_orthogonality := TrmRel.introduction_elimination_orthogonality
  scr_decomposition := TrmRel.scr_decomposition
  subst_introduction_oplaxity := fun a b _ => TrmRel.subst_introduction_oplaxity a b
  subst_elimination_oplaxity := TrmRel.subst_elimination_oplaxity
  box_elimination_oplaxity := TrmRel.box_elimination_oplaxity


end LeanTra.Instances.PeanoArithmetic
