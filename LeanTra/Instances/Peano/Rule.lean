/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
module

public import LeanTra.Instances.Peano.OperationalDecomposition
public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Metatheory.Confluence.Local
public import LeanTra.Metatheory.Determinism.BigStep

/-!
# The Peano rewrite rules

The four defining equations of Peano arithmetic as a `TrmRel`, the five rule-level local
hypotheses required by the bridge theorem, and the resulting confluence and big-step
determinism results.

## Main definitions
* `TrmRel.rule`: the four Peano rewrite rules packaged as a single `TrmRel`.

## Main statements
* `TrmRel.rule_isReduction`, `TrmRel.rule_isSubstitutiveAtIdentity`,
  `TrmRel.rule_isDeterministic`, `TrmRel.rule_gip`, `TrmRel.rule_gcp`:
  the five rule-level local hypotheses of the bridge theorem.
* `TrmRel.rule_confluent`: confluence of parallel reduction via
  `LeanTra.Confluence.local_confluence`.
* `TrmRel.rule_boxed_gip`, `TrmRel.rule_boxed_isDeterministic`: the Gentzen inversion and
  determinism of the closed part of the rule.
* `TrmRel.rule_bigStep_determinism`: determinism of big-step Peano-arithmetic evaluation.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Instances.PeanoArithmetic

/-!
Everything above was preparation. We can now state the primitive
reduction of Peano arithmetic as a `TrmRel`: the disjunction of the
four defining rewrite rules, `plus(zero, n) → n`,
`plus(succ m, n) → succ (plus m n)`, `mult(zero, n) → zero`, and
`mult(succ m, n) → plus (mult m n) n`. Renaming-closure of the family
is checked by mapping the free variables of each pattern under the
renaming, a computation of one line per disjunct.

The next five theorems discharge, on this concrete `rule`, the five
local hypotheses required by the abstract bridge theorem
`local_confluence`. `IsReduction` states that a variable cannot reduce,
which is immediate since every rule pattern has a compound left-hand
side. `IsSubstitutiveAtIdentity` states that the rule is preserved by
substitution along a pointwise-equal substitution; it splits into four
cases, each a small `Tm.subst` computation. `IsDeterministic` states
that the four rule patterns are pairwise non-overlapping, which gives
a 4×4 = 16 sub-case matrix with twelve shape-conflicts and four honest
sub-cases. `GIP` (Gentzen's Inversion Principle) picks, for each of the
four rule patterns, the redex itself as the witness of
`elimination (introduction 1) 1`, since every rule LHS is an
elimination form on an introduction-form major. `GCP` (Gentzen's
Conservation Principle) is the technically heaviest of the five: it
splits on 2 (elim-plus / elim-mult) × 4 (rule patterns) = 8 sub-cases,
four of which are immediate shape-conflicts (an elim-plus followed by
a mult-rule and vice versa), and four of which need real work — the
two "succ-side" ones use a `Bool` context to encode a two-slot
substitution template, while the two "zero-side" ones get away with a
trivial one-slot substitution over `Unit`. Once all five hold, the
bridge theorem delivers confluence of parallel reduction as a
one-liner: `rule_confluent := local_confluence rule_isReduction …`.
-/

namespace TrmRel

/-- The primitive reduction: the four Peano defining equations,
```
plus(zero,   n) → n
plus(succ m, n) → succ (plus m n)
mult(zero,   n) → zero
mult(succ m, n) → plus (mult m n) n
```
packaged as a single `TrmRel` by disjunction. All five bridge-theorem
hypotheses below (`IsReduction`, `IsSubstitutiveAtIdentity`,
`IsDeterministic`, `GIP`, `GCP`) are stated against this `TrmRel` and
proceed by `rcases` on the disjunction. -/
def rule : TrmRel := {
  rel := fun Γ t s =>
    (∃ n : Tm Γ, t = Tm.plus Tm.zero n ∧ s = n) ∨
    (∃ x y : Tm Γ, t = Tm.plus (Tm.succ x) y ∧ s = Tm.succ (Tm.plus x y)) ∨
    (∃ n : Tm Γ, t = Tm.mult Tm.zero n ∧ s = Tm.zero) ∨
    (∃ x y : Tm Γ, t = Tm.mult (Tm.succ x) y ∧
                    s = Tm.plus (Tm.mult x y) y)
  ren_closed := by
    intro Γ Δ f t s h
    rcases h with ⟨n, ht, hs⟩
                | ⟨x, y, ht, hs⟩
                | ⟨n, ht, hs⟩
                | ⟨x, y, ht, hs⟩
    · refine Or.inl ⟨n.ren f, ?_, ?_⟩
      · rw [ht]; simp
      · rw [hs]
    · refine Or.inr (Or.inl ⟨x.ren f, y.ren f, ?_, ?_⟩)
      · rw [ht]; simp
      · rw [hs]; simp
    · refine Or.inr (Or.inr (Or.inl ⟨n.ren f, ?_, ?_⟩))
      · rw [ht]; simp
      · rw [hs]; simp
    · refine Or.inr (Or.inr (Or.inr ⟨x.ren f, y.ren f, ?_, ?_⟩))
      · rw [ht]; simp
      · rw [hs]; simp
}

@[simp] theorem rule_rel {Γ} {t s : Tm Γ} :
    (rule : TrmRel).rel Γ t s ↔
      (∃ n : Tm Γ, t = Tm.plus Tm.zero n ∧ s = n) ∨
      (∃ x y : Tm Γ, t = Tm.plus (Tm.succ x) y ∧
                      s = Tm.succ (Tm.plus x y)) ∨
      (∃ n : Tm Γ, t = Tm.mult Tm.zero n ∧ s = Tm.zero) ∨
      (∃ x y : Tm Γ, t = Tm.mult (Tm.succ x) y ∧
                      s = Tm.plus (Tm.mult x y) y) := Iff.rfl

theorem rule_isReduction : LeanTra.Confluence.IsReduction (rule : TrmRel) := by
  change (TRA.varDiag * rule : TrmRel) = ⊥
  ext Γ t v
  constructor
  · rintro ⟨m, ⟨z, rfl, rfl⟩, hrule⟩
    rcases hrule with ⟨_, hm, _⟩
                    | ⟨_, _, hm, _⟩
                    | ⟨_, hm, _⟩
                    | ⟨_, _, hm, _⟩ <;> cases hm
  · intro h; exact h.elim

theorem rule_isSubstitutiveAtIdentity :
    LeanTra.Confluence.IsSubstitutiveAtIdentity (rule : TrmRel) := by
  change (TRA.subst rule 1 : TrmRel) ≤ rule
  rintro Θ u v ⟨Γ, t, s, τ, σ, rfl, rfl, hrule, hτσ⟩
  have hτσ_eq : τ = σ := funext hτσ
  subst hτσ_eq
  rcases hrule with ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
                  | ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
  · refine Or.inl ⟨n.subst τ, ?_, ?_⟩
    · rw [ht]; simp
    · rw [hs]
  · refine Or.inr (Or.inl ⟨x.subst τ, y.subst τ, ?_, ?_⟩)
    · rw [ht]; simp
    · rw [hs]; simp
  · refine Or.inr (Or.inr (Or.inl ⟨n.subst τ, ?_, ?_⟩))
    · rw [ht]; simp
    · rw [hs]; simp
  · refine Or.inr (Or.inr (Or.inr ⟨x.subst τ, y.subst τ, ?_, ?_⟩))
    · rw [ht]; simp
    · rw [hs]; simp

theorem rule_isDeterministic : LeanTra.Algebra.IsDeterministic (rule : TrmRel) := by
  change ((rule : TrmRel)ᵒ * rule) ≤ 1
  rintro Γ t t' ⟨m, h1, h2⟩
  -- h1 : rule^o (t, m) = rule (m, t); h2 : rule (m, t').
  -- 4 × 4 = 16 sub-cases; the diagonal ones give t = t', the off-diagonal
  -- ones contradict the shape of `m`.
  rcases h1 with ⟨n, hm_eq, rfl⟩
              | ⟨x, y, hm_eq, rfl⟩
              | ⟨n, hm_eq, rfl⟩
              | ⟨x, y, hm_eq, rfl⟩ <;>
    rcases h2 with ⟨n', hm_eq', rfl⟩
                | ⟨x', y', hm_eq', rfl⟩
                | ⟨n', hm_eq', rfl⟩
                | ⟨x', y', hm_eq', rfl⟩
  -- (plus-zero, plus-zero)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨_, rfl⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    rfl
  -- (plus-zero, plus-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    cases hz
  -- (plus-zero, mult-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (plus-zero, mult-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (plus-succ, plus-zero)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    cases hz
  -- (plus-succ, plus-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hs, rfl⟩ := Tm.plus.injEq _ _ _ _ |>.mp this
    have : x = x' := Tm.succ.inj hs
    subst this; rfl
  -- (plus-succ, mult-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (plus-succ, mult-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-zero, plus-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-zero, plus-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-zero, mult-zero)
  · rfl
  -- (mult-zero, mult-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.mult.injEq _ _ _ _ |>.mp this
    cases hz
  -- (mult-succ, plus-zero)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-succ, plus-succ)
  · cases hm_eq.symm.trans hm_eq'
  -- (mult-succ, mult-zero)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hz, _⟩ := Tm.mult.injEq _ _ _ _ |>.mp this
    cases hz
  -- (mult-succ, mult-succ)
  · have := hm_eq.symm.trans hm_eq'
    obtain ⟨hs, rfl⟩ := Tm.mult.injEq _ _ _ _ |>.mp this
    have : x = x' := Tm.succ.inj hs
    subst this; rfl

theorem rule_gip : LeanTra.Metatheory.GIP (rule : TrmRel) := by
  intro Γ t s hrule
  rcases hrule with ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
                  | ⟨n, ht, hs⟩
                  | ⟨x, y, ht, hs⟩
  · -- plus-zero: intermediate = t = plus zero n.
    subst ht; subst hs
    exact ⟨Tm.plus Tm.zero s,
           Or.inl ⟨Tm.zero, Tm.zero, s, s, rfl, rfl,
                   Or.inl ⟨rfl, rfl⟩, rfl⟩,
           Or.inl ⟨s, rfl, rfl⟩⟩
  · -- plus-succ: intermediate = t = plus (succ x) y.
    subst ht; subst hs
    exact ⟨Tm.plus (Tm.succ x) y,
           Or.inl ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           Or.inr (Or.inl ⟨x, y, rfl, rfl⟩)⟩
  · -- mult-zero: intermediate = t = mult zero n.
    subst ht; subst hs
    exact ⟨Tm.mult Tm.zero n,
           Or.inr ⟨Tm.zero, Tm.zero, n, n, rfl, rfl,
                   Or.inl ⟨rfl, rfl⟩, rfl⟩,
           Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))⟩
  · -- mult-succ: intermediate = t = mult (succ x) y.
    subst ht; subst hs
    exact ⟨Tm.mult (Tm.succ x) y,
           Or.inr ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           Or.inr (Or.inr (Or.inr ⟨x, y, rfl, rfl⟩))⟩

theorem rule_gcp : LeanTra.Metatheory.GCP (rule : TrmRel) := by
  intro rx hcompat
  change (OperationalDecomposition.elimination (TRA.cr rx) rx : TrmRel)
           * (rule : TrmRel)
       ≤ (rule : TrmRel) * TRA.subst rx rx
  -- Compatibility gives rx-reflexivity on any `t`, since `varDiag ⊔ scr rx ≤ rx`
  -- and by structural induction on `t` we cover every case.
  have hvar_refl : ∀ (Γ : Type) (x : Γ), rx.rel Γ (Tm.var x) (Tm.var x) :=
    fun _ x => hcompat _ _ _ (Or.inl ⟨x, rfl, rfl⟩)
  have hzero_refl : ∀ (Γ : Type), rx.rel Γ Tm.zero Tm.zero :=
    fun _ => hcompat _ _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  rintro Γ t v ⟨m, helim, hrule⟩
  rcases helim with ⟨m₁, m₂, n₁, n₂, rfl, hm_eq, hmaj, hmin⟩
                  | ⟨m₁, m₂, n₁, n₂, rfl, hm_eq, hmaj, hmin⟩
  -- ELIM-PLUS branch: t = plus m₁ n₁, m = plus m₂ n₂
  · rcases hrule with ⟨n_ru, hm_ru, hv⟩
                    | ⟨x', y', hm_ru, hv⟩
                    | ⟨_, hm_ru, _⟩
                    | ⟨_, _, hm_ru, _⟩
    · -- plus-zero rule: m₂ = zero, n₂ = n_ru, v = n_ru
      -- `subst hv` eliminates `n_ru` (Lean prefers to substitute the
      -- pattern-bound existential witness); `v` is what survives.
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold TRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨hm1, _⟩
                      | ⟨_, _, _, hz, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · -- m₁ = zero, t = plus zero n₁, reduce via plus-zero to n₁
          subst hm1
          refine ⟨n₁, Or.inl ⟨n₁, rfl, rfl⟩, ?_⟩
          -- subst rx rx (n₁, v) via the trivial `Unit` context.
          -- After `subst hv` earlier, `n_ru` was eliminated and `v` is
          -- what identifies the target minor slot.
          refine ⟨Unit, Tm.var (), Tm.var (),
                  fun _ => n₁, fun _ => _, rfl, rfl,
                  hvar_refl _ (), fun _ => hmin⟩
        · cases hz
        · cases hz
        · cases hz
    · -- plus-succ rule: m₂ = succ x', n₂ = y'
      -- `subst hv` eliminates `v` (LHS-var, RHS compound). `subst hn2`
      -- with `hn2 : n₂ = y'` eliminates `y'` (pattern-bound); `n₂`
      -- survives. Likewise `subst hxu'` with `hxu' : x' = u'` eliminates
      -- `u'`; `x'` survives.
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.plus.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold TRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨_, hz⟩
                      | ⟨u, u', hm1_eq, hux, hrx⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · cases hz
        · -- m₁ = succ u, succ x' = succ u'; note y' → n₂ and u' → x'
          subst hm1_eq
          have hxu' : x' = u' := Tm.succ.inj hux
          subst hxu'
          refine ⟨Tm.succ (Tm.plus u n₁),
                  Or.inr (Or.inl ⟨u, n₁, rfl, rfl⟩), ?_⟩
          -- Bool context: false ↦ major body, true ↦ minor
          refine ⟨Bool,
                  Tm.succ (Tm.plus (Tm.var false) (Tm.var true)),
                  Tm.succ (Tm.plus (Tm.var false) (Tm.var true)),
                  fun b : Bool => if b then n₁ else u,
                  fun b : Bool => if b then n₂ else x',
                  rfl, rfl, ?_, ?_⟩
          · have h_scr_plus :
                (TRA.scr rx : TrmRel).rel Bool
                  (Tm.plus (Tm.var false) (Tm.var true))
                  (Tm.plus (Tm.var false) (Tm.var true)) :=
              Or.inr (Or.inr (Or.inl
                ⟨_, _, _, _, rfl, rfl, hvar_refl _ _, hvar_refl _ _⟩))
            have h_rx_plus := hcompat _ _ _ (Or.inr h_scr_plus)
            have h_scr_succ :
                (TRA.scr rx : TrmRel).rel Bool
                  (Tm.succ (Tm.plus (Tm.var false) (Tm.var true)))
                  (Tm.succ (Tm.plus (Tm.var false) (Tm.var true))) :=
              Or.inr (Or.inl ⟨_, _, rfl, rfl, h_rx_plus⟩)
            exact hcompat _ _ _ (Or.inr h_scr_succ)
          · intro b
            cases b <;> simp [*]
        · cases hz
        · cases hz
    · -- mult-zero rule but plus intermediate: impossible
      cases hm_eq.symm.trans hm_ru
    · -- mult-succ: impossible
      cases hm_eq.symm.trans hm_ru
  -- ELIM-MULT branch: t = mult m₁ n₁, m = mult m₂ n₂
  · rcases hrule with ⟨_, hm_ru, _⟩
                    | ⟨_, _, hm_ru, _⟩
                    | ⟨n_ru, hm_ru, hv⟩
                    | ⟨x', y', hm_ru, hv⟩
    · cases hm_eq.symm.trans hm_ru
    · cases hm_eq.symm.trans hm_ru
    · -- mult-zero rule: m₂ = zero, n₂ = n_ru, v = zero
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.mult.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold TRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨hm1, _⟩
                      | ⟨_, _, _, hz, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · -- m₁ = zero, t = mult zero n₁, reduce via mult-zero to zero
          subst hm1
          refine ⟨Tm.zero,
                  Or.inr (Or.inr (Or.inl ⟨n₁, rfl, rfl⟩)), ?_⟩
          -- subst rx rx (zero, zero) via closed constant
          exact ⟨Unit, Tm.zero, Tm.zero,
                 fun _ => Tm.zero, fun _ => Tm.zero, rfl, rfl,
                 hzero_refl _, fun _ => hzero_refl _⟩
        · cases hz
        · cases hz
        · cases hz
    · -- mult-succ rule: m₂ = succ x', n₂ = y'
      -- Same substitution convention as the plus-succ branch: `y' → n₂`,
      -- `u' → x'`.
      subst hv
      have heq := hm_eq.symm.trans hm_ru
      obtain ⟨hm2, hn2⟩ := Tm.mult.injEq _ _ _ _ |>.mp heq
      subst hm2; subst hn2
      unfold TRA.cr at hmaj
      rcases hmaj with ⟨z, _, hz⟩ | hscr
      · cases hz
      · rcases hscr with ⟨_, hz⟩
                      | ⟨u, u', hm1_eq, hux, hrx⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
                      | ⟨_, _, _, _, _, hz, _, _⟩
        · cases hz
        · -- m₁ = succ u, succ x' = succ u'
          subst hm1_eq
          have hxu' : x' = u' := Tm.succ.inj hux
          subst hxu'
          refine ⟨Tm.plus (Tm.mult u n₁) n₁,
                  Or.inr (Or.inr (Or.inr ⟨u, n₁, rfl, rfl⟩)), ?_⟩
          -- Bool context: false ↦ major body, true ↦ minor (also
          -- reappears in outer plus's minor slot)
          refine ⟨Bool,
                  Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true),
                  Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true),
                  fun b : Bool => if b then n₁ else u,
                  fun b : Bool => if b then n₂ else x',
                  rfl, rfl, ?_, ?_⟩
          · have h_scr_mult :
                (TRA.scr rx : TrmRel).rel Bool
                  (Tm.mult (Tm.var false) (Tm.var true))
                  (Tm.mult (Tm.var false) (Tm.var true)) :=
              Or.inr (Or.inr (Or.inr
                ⟨_, _, _, _, rfl, rfl, hvar_refl _ _, hvar_refl _ _⟩))
            have h_rx_mult := hcompat _ _ _ (Or.inr h_scr_mult)
            have h_scr_plus :
                (TRA.scr rx : TrmRel).rel Bool
                  (Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true))
                  (Tm.plus (Tm.mult (Tm.var false) (Tm.var true)) (Tm.var true)) :=
              Or.inr (Or.inr (Or.inl
                ⟨_, _, _, _, rfl, rfl, h_rx_mult, hvar_refl _ _⟩))
            exact hcompat _ _ _ (Or.inr h_scr_plus)
          · intro b
            cases b <;> simp [*]
        · cases hz
        · cases hz

/-- Confluence of parallel reduction on the entire four-rule
Peano-arithmetic reduction system. Obtained by feeding the five local
hypotheses proved above to the abstract bridge theorem
`local_confluence`; no Peano-specific tactic appears in the body. -/
theorem rule_confluent :
    LeanTra.Algebra.IsConfluent (LeanTra.Confluence.parRed (rule : TrmRel)) :=
  LeanTra.Confluence.local_confluence
    rule_isReduction
    rule_isSubstitutiveAtIdentity
    rule_isDeterministic
    rule_gip
    rule_gcp

/-! ### Determinism of big-step evaluation

The metatheorem `LeanTra.Determinism.bigStep_determinism` concludes
`(a^⇓)ᵒ * a^⇓ ≤ Δκ` from `GIP`, `IsClosed` and `IsDeterministic` of
the rule. Plain `rule` does not satisfy `IsClosed`: it fires between
open terms too — e.g. `plus zero (var x)` with `x` free reduces to
`var x`. The natural instantiation is on the closed part of the
rule, `TRA.box rule`, which relates only closed terms; its three
hypotheses are discharged here. `IsClosed (TRA.box rule)` is
`TRA.box_isClosed`. `IsDeterministic (TRA.box rule)` follows from
`rule_isDeterministic` and `TRA.box_le`. `GIP (TRA.box rule)` is
proved directly by the same four-way case analysis as `rule_gip`,
adapted to carry the closedness bookkeeping through the two `j`
factors of `TRA.box`. The final theorem `rule_bigStep_determinism`
is then a one-line application of the metatheorem. -/

/-- Gentzen inversion for the closed part of the rule: every closed
step factors on the left through an elimination with an introduction
form in the major slot, with the closedness of the source preserved.
Same four-case argument as `rule_gip`, threading closedness through
the two `j` factors of `TRA.box`. -/
theorem rule_boxed_gip : LeanTra.Metatheory.GIP (TRA.box (rule : TrmRel)) := by
  rintro Γ t s ⟨w, ⟨w', ⟨rfl, t₀, ht_close⟩, hrule⟩, ⟨rfl, s₀, hs_close⟩⟩
  -- Preserve `hs`/`hs'`/etc. as equational hypotheses instead of substituting
  -- them away: the plus-zero and mult-zero cases have `s = n` with `n` and `s`
  -- both fresh, and Lean's `subst` heuristic on that pair renames the surviving
  -- variable in a way that makes the term-level witness unreadable.
  rcases hrule with ⟨n, rfl, hs⟩
                  | ⟨x, y, rfl, rfl⟩
                  | ⟨n, rfl, hs⟩
                  | ⟨x, y, rfl, rfl⟩
  · -- plus-zero: source `plus zero n`, target `n` (via `hs : s = n`).
    refine ⟨Tm.plus Tm.zero n,
            Or.inl ⟨Tm.zero, Tm.zero, n, n, rfl, rfl,
                    Or.inl ⟨rfl, rfl⟩, rfl⟩,
            ⟨n,
              ⟨Tm.plus Tm.zero n, ⟨rfl, t₀, ht_close⟩,
                Or.inl ⟨n, rfl, rfl⟩⟩,
              ⟨hs.symm, s₀, hs.symm ▸ hs_close⟩⟩⟩
  · -- plus-succ: source `plus (succ x) y`, target `succ (plus x y)`.
    exact ⟨Tm.plus (Tm.succ x) y,
           Or.inl ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           ⟨Tm.succ (Tm.plus x y),
             ⟨Tm.plus (Tm.succ x) y, ⟨rfl, t₀, ht_close⟩,
               Or.inr (Or.inl ⟨x, y, rfl, rfl⟩)⟩,
             ⟨rfl, s₀, hs_close⟩⟩⟩
  · -- mult-zero: source `mult zero n`, target `zero` (via `hs : s = zero`).
    refine ⟨Tm.mult Tm.zero n,
            Or.inr ⟨Tm.zero, Tm.zero, n, n, rfl, rfl,
                    Or.inl ⟨rfl, rfl⟩, rfl⟩,
            ⟨Tm.zero,
              ⟨Tm.mult Tm.zero n, ⟨rfl, t₀, ht_close⟩,
                Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))⟩,
              ⟨hs.symm, s₀, hs.symm ▸ hs_close⟩⟩⟩
  · -- mult-succ: source `mult (succ x) y`, target `plus (mult x y) y`.
    exact ⟨Tm.mult (Tm.succ x) y,
           Or.inr ⟨Tm.succ x, Tm.succ x, y, y, rfl, rfl,
                   Or.inr ⟨x, x, rfl, rfl, rfl⟩, rfl⟩,
           ⟨Tm.plus (Tm.mult x y) y,
             ⟨Tm.mult (Tm.succ x) y, ⟨rfl, t₀, ht_close⟩,
               Or.inr (Or.inr (Or.inr ⟨x, y, rfl, rfl⟩))⟩,
             ⟨rfl, s₀, hs_close⟩⟩⟩

/-- The closed part of the rule is deterministic: `(□r)ᵒ * □r ≤ 1`.
Immediate from `rule_isDeterministic` and the deflationarity `□a ≤ a`
on both sides. -/
theorem rule_boxed_isDeterministic :
    LeanTra.Algebra.IsDeterministic (TRA.box (rule : TrmRel)) := by
  change ((TRA.box (rule : TrmRel))ᵒ * TRA.box rule) ≤ 1
  calc (TRA.box (rule : TrmRel))ᵒ * TRA.box rule
      ≤ (rule : TrmRel)ᵒ * TRA.box rule :=
        mul_le_mul' (IsInvolutiveQuantale.converse_monotonicity (TRA.box_le _)) le_rfl
    _ ≤ (rule : TrmRel)ᵒ * rule :=
        mul_le_mul' le_rfl (TRA.box_le _)
    _ ≤ 1 := rule_isDeterministic

/-- **Determinism of big-step Peano-arithmetic evaluation.** For the
closed part of the four-rule reduction system,
`(r^⇓)ᵒ * r^⇓ ≤ Δκ`. Direct instantiation of
`LeanTra.Determinism.bigStep_determinism` at `TRA.box rule`, with
the three hypotheses discharged just above. -/
theorem rule_bigStep_determinism :
    (LeanTra.Determinism.bigStepEvaluation (TRA.box (rule : TrmRel)))ᵒ
        * LeanTra.Determinism.bigStepEvaluation (TRA.box rule)
      ≤ (OperationalDecomposition.valueCoreflexive : TrmRel) :=
  LeanTra.Determinism.bigStep_determinism
    rule_boxed_gip
    (TRA.box_isClosed _)
    rule_boxed_isDeterministic

end TrmRel

end LeanTra.Instances.PeanoArithmetic
