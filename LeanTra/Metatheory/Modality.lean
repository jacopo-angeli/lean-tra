/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Derived

/-!
# Modalities on Syntax Relation Algebras

Modalities on the *derived* `SRA.box a := SRA.j * a * SRA.j` (see the
design note in `Structure/SRA.lean`). From the four `j` axioms
(`j_coreflexivity`, `j_symmetry`, `j_cotransitivity`, `j_varDiag_orthogonality`)
we discharge, in this order and each unconditionally:
`j_mul_j`, `j_converse`, `box_eq` (`rfl`), `box_le`, `box_box`,
`box_mono`, `box_mul_box_eq_box_mul_left`,
`box_mul_box_eq_box_mul_right`, `box_mul_box_le`, `box_converse`,
`box_sSup`, `box_sup`, `box_varDiag_eq_bot`. Then the diamond
`dia a := sSup {x | box x ≤ a}`, its monotonicity `dia_mono`, the
adjunction `box_le_iff` (no `hjoin` hypothesis), and the fixed-point
transfer lemma `box_lfp` — all sorry-free.

The old axiom `box_subst_le : subst (box a) b ≤ box a` does NOT
survive: as documented in the section body, no condition on `j` alone
yields it through the oplax `subst_compositionality_oplax`, and the intended
context-indexed model (`Instances/FirstOrder`) exhibits a concrete
`SynRel` refuting the inequality.

Closed relations: `IsClosed a := a ≤ box a`, characterisation
`isClosed_iff`, and the fact that `box a` and `⊥` are always closed.
All unconditional.

## Status — open items

* `SubstJClosed` — `∀ a, IsClosed (subst a j)` (`T[j]` closed).
  Candidate predicate (`SRA.SubstJClosed`, this file); true in the
  context-indexed term model
  (`LeanTra.Instances.FirstOrder.SynRel.substJClosed`); not derivable
  from the current axioms; no consumer yet.
* `(box a)[b] ≤ box a` — dropped from the class. False in the
  context-indexed term model; obstruction and counterexample recorded
  in the "Investigation: the dropped axiom `box_subst_le`" block below.
* `box (a * b) ≤ box a * box b` — REFUTED
  (`LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`).
  LICS'26 §3.2.1 asserts the equality `□(ϕ;ψ) = □ϕ;□ψ`; under the
  derived `box := j * · * j` only the lax half `SRA.box_mul_box_le`
  survives. This is expected to block the direct application of
  `SRA.box_lfp` to the operational-semantics evaluation recursor.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

namespace SRA

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-! ### Modalities

`□a := SRA.j * a * SRA.j`, defined in `Structure/SRA.lean` (see the design
note there for why the old primitive-`□` axiomatisation was replaced). This
section derives all eleven of the old box laws from the four `j` axioms
(`j_coreflexivity`, `j_symmetry`, `j_cotransitivity`, `j_varDiag_orthogonality`) and
nothing else — no `sorry`, no additional hypothesis. -/

/-- `j * j = j`. `≤` from `j_coreflexivity` (`j*j ≤ 1*j = j`); `≥` is
`j_cotransitivity`. -/
@[simp]
theorem j_mul_j : (SRA.j : α) * SRA.j = SRA.j := by
  refine le_antisymm ?_ SRA.j_cotransitivity
  calc (SRA.j : α) * SRA.j
      ≤ 1 * SRA.j := mul_le_mul' SRA.j_coreflexivity le_rfl
    _ = SRA.j := one_mul _

/-- `jᵒ = j`: same one-liner as `varDiag_converse`, from `j_symmetry`
plus involutivity of converse. -/
@[simp]
theorem j_converse : (SRA.j : α)ᵒ = SRA.j := by
  refine le_antisymm SRA.j_symmetry ?_
  have h : (SRA.j : α)ᵒᵒ ≤ (SRA.j : α)ᵒ :=
    IsInvolutiveQuantale.converse_monotonicity SRA.j_symmetry
  rwa [IsInvolutiveQuantale.converse_involutivity] at h

/-- The advisor's identity `□T = j * T * j`, held now by `rfl` because
`box` is defined as `j * · * j` (see `Structure/SRA.lean`). Kept as a
lemma so downstream code can cite it under its familiar name. -/
theorem box_eq (a : α) : SRA.box a = SRA.j * a * SRA.j := rfl

/-- `□a ≤ a`. Two applications of `j_coreflexivity`. -/
theorem box_le (a : α) : SRA.box a ≤ a := by
  change SRA.j * a * SRA.j ≤ a
  calc SRA.j * a * SRA.j
      ≤ 1 * a * 1 := mul_le_mul' (mul_le_mul' SRA.j_coreflexivity le_rfl) SRA.j_coreflexivity
    _ = a := by rw [one_mul, mul_one]

/-- `□(□a) = □a`. Collapse of the two `j*j` blocks via `j_mul_j`. -/
theorem box_box (a : α) : SRA.box (SRA.box a) = SRA.box a := by
  change SRA.j * (SRA.j * a * SRA.j) * SRA.j = SRA.j * a * SRA.j
  rw [← mul_assoc SRA.j (SRA.j * a) SRA.j] at *
  -- goal: SRA.j * (SRA.j * a) * SRA.j * SRA.j = SRA.j * a * SRA.j
  rw [← mul_assoc SRA.j SRA.j a]
  -- goal: SRA.j * SRA.j * a * SRA.j * SRA.j = SRA.j * a * SRA.j
  rw [j_mul_j, mul_assoc (SRA.j * a) SRA.j SRA.j, j_mul_j]

/-- `□` is monotone: from monotonicity of `*`. -/
theorem box_mono ⦃a b : α⦄ (h : a ≤ b) : SRA.box a ≤ SRA.box b := by
  change SRA.j * a * SRA.j ≤ SRA.j * b * SRA.j
  exact mul_le_mul' (mul_le_mul' le_rfl h) le_rfl

/-- Left absorption: `□a * □b = □(□a * b)`. Both sides reduce to
`j * a * j * b * j` after collapsing `j * j`. -/
theorem box_mul_box_eq_box_mul_left (a b : α) :
    SRA.box a * SRA.box b = SRA.box (SRA.box a * b) := by
  change SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
       = SRA.j * (SRA.j * a * SRA.j * b) * SRA.j
  have hL : SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc (SRA.j * a * SRA.j) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a * SRA.j) SRA.j b,
        mul_assoc (SRA.j * a) SRA.j SRA.j, j_mul_j]
  have hR : SRA.j * (SRA.j * a * SRA.j * b) * SRA.j
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc SRA.j (SRA.j * a * SRA.j) b,
        ← mul_assoc SRA.j (SRA.j * a) SRA.j,
        ← mul_assoc SRA.j SRA.j a, j_mul_j]
  rw [hL, hR]

/-- Right absorption: `□a * □b = □(a * □b)`. Symmetric to
`box_mul_box_eq_box_mul_left`. -/
theorem box_mul_box_eq_box_mul_right (a b : α) :
    SRA.box a * SRA.box b = SRA.box (a * SRA.box b) := by
  change SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
       = SRA.j * (a * (SRA.j * b * SRA.j)) * SRA.j
  have hL : SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc (SRA.j * a * SRA.j) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a * SRA.j) SRA.j b,
        mul_assoc (SRA.j * a) SRA.j SRA.j, j_mul_j]
  have hR : SRA.j * (a * (SRA.j * b * SRA.j)) * SRA.j
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc SRA.j a (SRA.j * b * SRA.j),
        ← mul_assoc (SRA.j * a) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a) SRA.j b,
        mul_assoc (SRA.j * a * SRA.j * b) SRA.j SRA.j, j_mul_j]
  rw [hL, hR]

/-- Lax multiplicativity: `□a * □b ≤ □(a * b)`. `box a * box b` collapses
to `j * a * j * b * j` via `j_mul_j`; then `j * b ≤ b` (from `j ≤ 1`)
delivers the middle `j` for free. -/
theorem box_mul_box_le (a b : α) : SRA.box a * SRA.box b ≤ SRA.box (a * b) := by
  change SRA.j * a * SRA.j * (SRA.j * b * SRA.j) ≤ SRA.j * (a * b) * SRA.j
  have hcollapse : SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
                 = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc (SRA.j * a * SRA.j) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a * SRA.j) SRA.j b,
        mul_assoc (SRA.j * a) SRA.j SRA.j, j_mul_j]
  rw [hcollapse]
  -- goal: SRA.j * a * SRA.j * b * SRA.j ≤ SRA.j * (a * b) * SRA.j
  calc SRA.j * a * SRA.j * b * SRA.j
      = SRA.j * a * (SRA.j * b) * SRA.j := by
        rw [mul_assoc (SRA.j * a) SRA.j b]
    _ ≤ SRA.j * a * (1 * b) * SRA.j :=
        mul_le_mul' (mul_le_mul' le_rfl
          (mul_le_mul' SRA.j_coreflexivity le_rfl)) le_rfl
    _ = SRA.j * a * b * SRA.j := by rw [one_mul]
    _ = SRA.j * (a * b) * SRA.j := by rw [mul_assoc SRA.j a b]

/-- `(□a)ᵒ = □(aᵒ)`. From `box_eq` and `j_converse`. -/
theorem box_converse (a : α) : (SRA.box a)ᵒ = SRA.box (aᵒ) := by
  change (SRA.j * a * SRA.j)ᵒ = SRA.j * aᵒ * SRA.j
  calc (SRA.j * a * SRA.j)ᵒ
      = (SRA.j)ᵒ * (SRA.j * a)ᵒ := IsInvolutiveQuantale.converse_compositionality _ _
    _ = (SRA.j)ᵒ * (aᵒ * (SRA.j)ᵒ) := by rw [IsInvolutiveQuantale.converse_compositionality]
    _ = SRA.j * (aᵒ * SRA.j) := by rw [j_converse]
    _ = SRA.j * aᵒ * SRA.j := (mul_assoc _ _ _).symm

/-- `□` preserves arbitrary joins. From `box_eq` and the two quantale
distributivity laws. -/
theorem box_sSup (s : Set α) : SRA.box (sSup s) = sSup (SRA.box '' s) := by
  refine le_antisymm ?_ ?_
  · rw [box_eq (sSup s), mul_assoc, sSup_mul_distrib, ← sSup_image,
        mul_sSup_distrib, ← sSup_image, Set.image_image]
    refine sSup_le_sSup ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    change SRA.box y = SRA.j * (y * SRA.j)
    rw [box_eq, mul_assoc]
  · refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact box_mono (le_sSup hy)

/-- Binary corollary of `box_sSup`: `□(a ⊔ b) = □a ⊔ □b`. -/
theorem box_sup (a b : α) : SRA.box (a ⊔ b) = SRA.box a ⊔ SRA.box b := by
  have h := box_sSup ({a, b} : Set α)
  rwa [sSup_pair, Set.image_pair, sSup_pair] at h

/-- `□Δη = ⊥`. From `j_varDiag_orthogonality` and `Quantale.bot_mul` (the
quantale fact that `⊥` is a left annihilator, itself a consequence of
`sSup_mul_distrib` on the empty set). -/
theorem box_varDiag_eq_bot : SRA.box (SRA.varDiag : α) = ⊥ := by
  change SRA.j * SRA.varDiag * SRA.j = ⊥
  refine le_antisymm ?_ bot_le
  calc SRA.j * SRA.varDiag * SRA.j
      ≤ (⊥ : α) * SRA.j := mul_le_mul' SRA.j_varDiag_orthogonality le_rfl
    _ = ⊥ := Quantale.bot_mul

/-! #### Investigation: the dropped axiom `box_subst_le`

Old class field: `subst (box a) b ≤ box a`. In the new presentation, this
would read `subst (j * a * j) b ≤ j * a * j`. It does **not** derive from
any condition on `j` alone, and it does **not** hold in the intended
context-indexed model.

Attempted derivation from `subst j b ≤ j` (the natural "j is
substitution-closed" axiom): every route through `SRA.subst_compositionality_oplax` — which
is oplax, `subst (a * a') (b * b') ≤ subst a b * subst a' b'` — leaks the
middle `a` factor into a `subst a c` term for some `c ∈ {1, b}` that is
never bounded above by `a` (only below, via `subst_varDiag_unit_right`
combined with `varDiag ≤ 1` giving `a ≤ subst a 1`). The final bound one
obtains is `box (subst a b)`, not `box a`; the two are incomparable in
general.

Model refutation. Take `α := SynRel S` (the context-indexed model,
`Instances/FirstOrder`) with `j` the identity on closed terms as per that
file. Define `a : SynRel S` by `a.rel Γ t s := Nonempty Γ` (renaming-closed
because `Nonempty Γ` transports to `Nonempty Δ` via the renaming's image).
Then at `Θ := Empty`, taking `Γ := Unit` inside the outer existential of
`subst (box a) b` and `t = s := Tm.close Unit t₀` for any closed `t₀`,
plus `b := ⊤`, LHS holds while RHS `= (box a).rel Empty t₀ t₀ =
closed t₀ ∧ closed t₀ ∧ Nonempty Empty = False`. So the axiom fails on
this instance. Dropped from the class rather than re-axiomatised. -/

/-! #### Diamond as the right adjoint of `□` -/

/-- Diamond `♦a := sSup {x | □x ≤ a}`, the pointwise right-adjoint
candidate for `□`. Given `box_sSup` (join-preservation of `□`), this
really is the right adjoint — see `box_le_iff` below. -/
def dia (a : α) : α := sSup {x | SRA.box x ≤ a}

/-- `♦` is monotone. -/
theorem dia_mono ⦃a a' : α⦄ (h : a ≤ a') : dia a ≤ dia a' :=
  sSup_le_sSup fun _ hx => le_trans hx h

/-- Easy half of the `□ ⊣ ♦` adjunction. -/
theorem le_dia_of_box_le {a b : α} (h : SRA.box a ≤ b) : a ≤ dia b :=
  le_sSup h

/-- The full `□ ⊣ ♦` adjunction. Uses `box_sSup` in the backward
direction to push `□` through the defining supremum of `♦b`. No
hypothesis argument — `box_sSup` is now unconditional. -/
theorem box_le_iff {a b : α} : SRA.box a ≤ b ↔ a ≤ dia b := by
  refine ⟨le_dia_of_box_le, fun h => ?_⟩
  calc SRA.box a
      ≤ SRA.box (dia b) := box_mono h
    _ = sSup (SRA.box '' {x | SRA.box x ≤ b}) := box_sSup _
    _ ≤ b := by
        refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hx

/-! ### Closed relations -/

/-- Closedness: a relation `a` is closed when it refines its own `box`. -/
def IsClosed (a : α) : Prop := a ≤ SRA.box a

/-- `a` is closed iff `□a = a`. -/
theorem isClosed_iff {a : α} : IsClosed a ↔ SRA.box a = a :=
  ⟨fun h => le_antisymm (box_le a) h, fun h => h.ge⟩

/-- `□a` is always closed. -/
theorem box_isClosed (a : α) : IsClosed (SRA.box a) := (box_box a).ge

/-- `⊥` is closed. -/
theorem isClosed_bot : IsClosed (⊥ : α) := bot_le

/-! ### Closed monotone functions and the transfer lemma -/

/-- A monotone `F` is closed when `□ ∘ F ≤ F ∘ □` pointwise. -/
def IsClosedFun (F : α →o α) : Prop := ∀ x, SRA.box (F x) ≤ F (SRA.box x)

/-- Composition `box ∘ F` bundled as an `OrderHom`. -/
def boxComp (F : α →o α) : α →o α where
  toFun x := SRA.box (F x)
  monotone' _ _ h := box_mono (F.mono h)

/-- Transfer lemma (the paper's Lemma 16): for a closed monotone `F`, `□`
commutes with the least fixed point — `□(μF) = μ(□∘F)`. Rides on
`box_box`, `box_mono`, `box_le` and the adjunction `box_le_iff` — all
unconditional now. -/
theorem box_lfp {F : α →o α} (hF : IsClosedFun F) :
    SRA.box F.lfp = (boxComp F).lfp := by
  refine le_antisymm ?_ ?_
  · refine box_le_iff.mpr ?_
    refine F.lfp_le ?_
    refine box_le_iff.mp ?_
    calc SRA.box (F (dia (boxComp F).lfp))
        = SRA.box (SRA.box (F (dia (boxComp F).lfp))) := (box_box _).symm
      _ ≤ SRA.box (F (SRA.box (dia (boxComp F).lfp))) := box_mono (hF _)
      _ ≤ SRA.box (F (boxComp F).lfp) :=
          box_mono (F.mono (box_le_iff.mpr le_rfl))
      _ = (boxComp F).lfp := (boxComp F).map_lfp
  · refine (boxComp F).lfp_le ?_
    change SRA.box (F (SRA.box F.lfp)) ≤ SRA.box F.lfp
    calc SRA.box (F (SRA.box F.lfp))
        ≤ SRA.box (F F.lfp) := box_mono (F.mono (box_le _))
      _ = SRA.box F.lfp := by rw [F.map_lfp]

-- Sanity: `box_le_iff` and `box_lfp` should now depend on only the
-- standard axioms — no `sorryAx`.
#print axioms SRA.box_le_iff
#print axioms SRA.box_lfp

/-! ### Experiment 3 — `T[j]` closed (`SubstJClosed`).
See `docs/modality-experiments.md#experiment-3`; term-model verification
in `LeanTra.Instances.FirstOrder.SynRel.substJClosed`. -/

/-- Candidate axiom: "substitution by `j` yields a closed relation."
Top-level `def`, NOT a class field. Not derivable from the current
axioms; true in the term model. -/
def SubstJClosed (α : Type*) [Monoid α] [CompleteLattice α]
    [IsQuantale α] [IsInvolutiveQuantale α] [SRA α] : Prop :=
  ∀ a : α, SRA.IsClosed (SRA.subst a SRA.j)

/-! ### Experiment 5 — `box (a * b) ≤ box a * box b`?
See `docs/modality-experiments.md#experiment-5`. Refuted in the term
model by `LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`;
only the lax half `box_mul_box_le` (above) survives under
`box := j * · * j`. -/

end SRA
