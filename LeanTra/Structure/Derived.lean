/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Structure.SRA
public import Mathlib.Order.FixedPoints

/-!
# Derived laws of Syntax Relation Algebras

Everything below is a theorem or `def` over `[SRA α]`; nothing is an axiom.
Grown across four passes, whose scope is reflected in the Contents list below.

## Contents

* Laws recovered from the three axioms removed as redundant when `SRA` was
  minimised: `varDiag_le_one`, `scr_one_le`, `subst_mono_left`, plus the full
  two-argument `subst_mono` combining the recovered left monotonicity with
  the axiom `subst_mono_right`.
* Basic laws of the derived operation `hat ·`: monotonicity, restatement of the
  fixed-point axiom (`cr_one`, `one_le_of_cr_le`), multiplicativity
  `cr a * cr b = cr (a * b)`, and converse `(cr a)ᵒ = cr (aᵒ)`.
* Two immediate consequences of `subst_sSup_left`: `subst ⊥ b = ⊥` and
  `subst (a ⊔ a') b = subst a b ⊔ subst a' b`.
* The Howe extension `·ᴴ` as the least solution of `x = cr x * a`
  (Knaster–Tarski via `OrderHom.lfp`), together with its fixed-point law,
  fixed-point induction, monotonicity (`howe_mono`), and uniqueness (the
  solution is not merely least — it is unique, proved via the left residual
  of composition).

* Closedness: `substResid b c := sSup {a | subst a b ≤ c}` — the right
  adjoint of `·[b]` from the Adjoint Functor Theorem, and the adjunction
  `subst_le_iff : subst a b ≤ c ↔ a ≤ substResid b c`. Notation `b » c`.
* Modalities on the *derived* `SRA.box a := SRA.j * a * SRA.j` (see the
  design note in `Structure/SRA.lean`). From the four `j` axioms
  (`j_le_one`, `j_converse_le`, `j_le_mul_self`, `j_mul_varDiag_le_bot`)
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
  yields it through the oplax `subst_mul_le`, and the intended
  context-indexed model (`Instances/FirstOrder`) exhibits a concrete
  `SynRel` refuting the inequality.

* Closed relations: `IsClosed a := a ≤ box a`, characterisation
  `isClosed_iff`, and the fact that `box a` and `⊥` are always closed.
  All unconditional.

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

/-! ### Laws recovered from removed axioms -/

/-- `Δη ≤ 1`: the variable co-equivalence is co-reflexive. -/
theorem varDiag_le_one : (SRA.varDiag : α) ≤ 1 :=
  le_sup_left.trans_eq SRA.varDiag_sup_scr_one_eq

/-- `tilde 1 ≤ 1`: the strict compatible refinement is oplax on the unit. -/
theorem scr_one_le : SRA.scr (1 : α) ≤ 1 :=
  le_sup_right.trans_eq SRA.varDiag_sup_scr_one_eq

/-- Left-argument monotonicity of substitution. -/
theorem subst_mono_left ⦃a a' b : α⦄ (h : a ≤ a') :
    SRA.subst a b ≤ SRA.subst a' b := by
  have key : SRA.subst (sSup ({a, a'} : Set α)) b
      = sSup ((fun x => SRA.subst x b) '' ({a, a'} : Set α)) :=
    SRA.subst_sSup_left _ _
  rw [sSup_pair, Set.image_pair, sSup_pair, sup_eq_right.mpr h] at key
  have hle : SRA.subst a b ≤ SRA.subst a b ⊔ SRA.subst a' b := le_sup_left
  rw [← key] at hle
  exact hle

/-- Full two-argument monotonicity of substitution. -/
theorem subst_mono ⦃a a' b b' : α⦄ (ha : a ≤ a') (hb : b ≤ b') :
    SRA.subst a b ≤ SRA.subst a' b' :=
  (subst_mono_left ha).trans (SRA.subst_mono_right hb)

/-! ### Symmetry of Δη -/

/-- `Δηᵒ = Δη`: the variable co-equivalence is symmetric on the nose, not
just oplaxly. -/
@[simp]
theorem varDiag_converse : (SRA.varDiag : α)ᵒ = SRA.varDiag := by
  refine le_antisymm SRA.varDiag_converse_le ?_
  have h : (SRA.varDiag : α)ᵒᵒ ≤ SRA.varDiagᵒ :=
    IsInvolutiveQuantale.converse_le_converse SRA.varDiag_converse_le
  rwa [IsInvolutiveQuantale.converse_involutive] at h

/-! ### Basic laws of compatible refinement -/

/-- `hat ·` is monotone. -/
theorem cr_mono ⦃a b : α⦄ (h : a ≤ b) : cr a ≤ cr b :=
  sup_le_sup_left (SRA.scr_mono h) _

/-- Fixed-point law for `hat ·`: `hat 1 = 1`. -/
@[simp]
theorem cr_one : cr (1 : α) = 1 := SRA.varDiag_sup_scr_one_eq

/-- Structural induction: `1` is the least pre-fixed point of `hat ·`. -/
theorem one_le_of_cr_le ⦃a : α⦄ (h : cr a ≤ a) : 1 ≤ a :=
  SRA.one_le_of_scr_sup_le h

/-! ### Orthogonality on the right -/

/-- Symmetric orthogonality: `tilde a * Δη ≤ ⊥`, derived from the axiomatic
left-orthogonality via converse. -/
theorem scr_mul_varDiag_le_bot (a : α) : SRA.scr a * SRA.varDiag ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_le_converse_iff,
      IsInvolutiveQuantale.converse_bot,
      IsInvolutiveQuantale.mul_converse,
      ← SRA.scr_converse, varDiag_converse]
  exact SRA.varDiag_mul_scr_le_bot _

/-! ### Multiplicativity of Δη and `hat ·` -/

/-- `Δη * Δη = Δη`: the variable co-equivalence is idempotent under
composition. -/
@[simp]
theorem varDiag_mul_self : (SRA.varDiag : α) * SRA.varDiag = SRA.varDiag := by
  refine le_antisymm ?_ SRA.varDiag_le_mul_self
  calc (SRA.varDiag : α) * SRA.varDiag
      ≤ 1 * SRA.varDiag := mul_le_mul' varDiag_le_one le_rfl
    _ = SRA.varDiag := one_mul _

/-- `hat ·` distributes over composition: `hat a * hat b = hat (a * b)`. -/
theorem cr_mul (a b : α) : cr a * cr b = cr (a * b) := by
  unfold cr
  rw [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
      Quantale.mul_sup_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_of_le_left varDiag_mul_self.le
    · exact (SRA.varDiag_mul_scr_le_bot b).trans bot_le
    · exact (scr_mul_varDiag_le_bot a).trans bot_le
    · rw [SRA.scr_mul]; exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_sup_of_le_left (le_sup_of_le_left SRA.varDiag_le_mul_self)
    · rw [SRA.scr_mul]
      exact le_sup_of_le_right (le_sup_of_le_right le_rfl)

/-- `hat ·` commutes with converse: `(hat a)ᵒ = hat (aᵒ)`. -/
@[simp]
theorem cr_converse (a : α) : (cr a)ᵒ = cr (aᵒ) := by
  unfold cr
  rw [IsInvolutiveQuantale.converse_sup, varDiag_converse, ← SRA.scr_converse]

/-! ### Substitution laws from join-preservation -/

/-- Substitution annihilates `⊥` on the left: `subst ⊥ b = ⊥`. -/
@[simp]
theorem subst_bot_left (b : α) : SRA.subst ⊥ b = ⊥ := by
  have h := SRA.subst_sSup_left (∅ : Set α) b
  simp only [Set.image_empty, sSup_empty] at h
  exact h

/-- Substitution preserves binary joins in the first argument. -/
theorem subst_sup_left (a a' b : α) :
    SRA.subst (a ⊔ a') b = SRA.subst a b ⊔ SRA.subst a' b := by
  have h := SRA.subst_sSup_left ({a, a'} : Set α) b
  simp only [sSup_pair, Set.image_pair] at h
  exact h

/-! ### Howe extension `·ᴴ` -/

/-- The Howe recursor: `x ↦ cr x * a`, bundled as an `OrderHom` so its least
fixed point can be taken via `OrderHom.lfp`. Internal helper for `howe`. -/
def howeStep (a : α) : α →o α where
  toFun x := cr x * a
  monotone' _ _ h := mul_le_mul_left (cr_mono h) a

/-- Howe extension `·ᴴ`: the unique solution of `x = cr x * a` (see
`howe_unique`). Constructed as the least fixed point via Knaster–Tarski;
uniqueness — proved below via residuals — turns "the least solution" into
"the only solution". -/
def howe (a : α) : α := (howeStep a).lfp

/-- Fixed-point law: `aᴴ` satisfies `aᴴ = cr aᴴ * a`. -/
theorem howe_fix (a : α) : howe a = cr (howe a) * a :=
  ((howeStep a).map_lfp).symm

/-- Fixed-point induction: `aᴴ` is below every pre-fixed point of the Howe
recursion. -/
theorem howe_le_of_cr_mul_le ⦃a x : α⦄ (h : cr x * a ≤ x) : howe a ≤ x :=
  (howeStep a).lfp_le h

/-- `·ᴴ` is monotone. -/
theorem howe_mono ⦃a b : α⦄ (h : a ≤ b) : howe a ≤ howe b := by
  refine howe_le_of_cr_mul_le ?_
  calc cr (howe b) * a
      ≤ cr (howe b) * b := mul_le_mul_right h _
    _ = howe b := (howe_fix b).symm

-- Design note on the *converse* of the Howe fixed-point equation.
-- Taking `·ᵒ` of both sides of `howe_fix` (`aᴴ = cr aᴴ * a`) and using
-- `mul_converse` and `cr_converse` gives
--     `(aᴴ)ᵒ = aᵒ * cr ((aᴴ)ᵒ)`,
-- i.e. the DUAL equation `x = a * cr x` — with the multiplication on the
-- other side. So `(aᴴ)ᵒ` is NOT `(aᵒ)ᴴ`: the two would agree only if the
-- Howe recursor were symmetric in the position of `cr`, and it is not.
-- This left/right asymmetry is why the paper later introduces the op-Howe
-- extension `·§` (least solution of `x = a * cr x`) for the congruence
-- proof; expect a mirror development in a future file.

/-- One direction of uniqueness: any two solutions of `x = cr x * a` are
mutually below each other. Argument via the left residual `⇨ₗ` and structural
induction on `hat ·`. -/
private theorem howe_solution_le {a b c : α}
    (hb : b = cr b * a) (hc : c = cr c * a) : b ≤ c := by
  rw [show b = 1 * b from (one_mul b).symm]
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine one_le_of_cr_le ?_
  refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
  calc cr (b ⇨ₗ c) * b
      = cr (b ⇨ₗ c) * (cr b * a) := by rw [← hb]
    _ = cr (b ⇨ₗ c) * cr b * a := (mul_assoc _ _ _).symm
    _ = cr ((b ⇨ₗ c) * b) * a := by rw [cr_mul]
    _ ≤ cr c * a := mul_le_mul_left
        (cr_mono (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl)) _
    _ = c := hc.symm

/-- Uniqueness: `x = cr x * a` has at most one solution — so `aᴴ` is not just
the *least* solution, it is the *only* solution. -/
theorem howe_unique {a b c : α} (hb : b = cr b * a) (hc : c = cr c * a) :
    b = c :=
  le_antisymm (howe_solution_le hb hc) (howe_solution_le hc hb)

/-- Usable form of uniqueness: anything satisfying the Howe equation *is* the
Howe extension. Lets an alternative construction be identified with `howe`. -/
theorem howe_eq_of_fix {a b : α} (hb : b = cr b * a) : b = howe a :=
  howe_unique hb (howe_fix a)

/-- The Howe extension fixes the identity: `1ᴴ = 1`. Derived, not assumed:
`1 = cr 1 * 1` by `cr_one` and `mul_one`, so `howe_eq_of_fix` identifies `1`
with `howe 1`. -/
theorem howe_one : howe (1 : α) = 1 :=
  (howe_eq_of_fix (by rw [cr_one, mul_one])).symm

/-! ### Closedness: residual of substitution -/

/-- Right adjoint of `·[b]`: the largest `a` such that `a[b] ≤ c`. -/
def substResid (b c : α) : α := sSup {a | SRA.subst a b ≤ c}

/-- The substitution/residual adjunction `·[b] ⊣ b » ·`. -/
theorem subst_le_iff {a b c : α} : SRA.subst a b ≤ c ↔ a ≤ substResid b c := by
  refine ⟨fun h => le_sSup h, fun h => ?_⟩
  calc SRA.subst a b
      ≤ SRA.subst (substResid b c) b := subst_mono_left h
    _ = sSup ((fun x => SRA.subst x b) '' {x | SRA.subst x b ≤ c}) :=
        SRA.subst_sSup_left _ _
    _ ≤ c := by
        refine sSup_le ?_
        rintro _ ⟨y, hy, rfl⟩
        exact hy

/-! ### Modalities

`□a := SRA.j * a * SRA.j`, defined in `Structure/SRA.lean` (see the design
note there for why the old primitive-`□` axiomatisation was replaced). This
section derives all eleven of the old box laws from the four `j` axioms
(`j_le_one`, `j_converse_le`, `j_le_mul_self`, `j_mul_varDiag_le_bot`) and
nothing else — no `sorry`, no additional hypothesis. -/

/-- `j * j = j`. `≤` from `j_le_one` (`j*j ≤ 1*j = j`); `≥` is
`j_le_mul_self`. -/
@[simp]
theorem j_mul_j : (SRA.j : α) * SRA.j = SRA.j := by
  refine le_antisymm ?_ SRA.j_le_mul_self
  calc (SRA.j : α) * SRA.j
      ≤ 1 * SRA.j := mul_le_mul' SRA.j_le_one le_rfl
    _ = SRA.j := one_mul _

/-- `jᵒ = j`: same one-liner as `varDiag_converse`, from `j_converse_le`
plus involutivity of converse. -/
@[simp]
theorem j_converse : (SRA.j : α)ᵒ = SRA.j := by
  refine le_antisymm SRA.j_converse_le ?_
  have h : (SRA.j : α)ᵒᵒ ≤ (SRA.j : α)ᵒ :=
    IsInvolutiveQuantale.converse_le_converse SRA.j_converse_le
  rwa [IsInvolutiveQuantale.converse_involutive] at h

/-- The advisor's identity `□T = j * T * j`, held now by `rfl` because
`box` is defined as `j * · * j` (see `Structure/SRA.lean`). Kept as a
lemma so downstream code can cite it under its familiar name. -/
theorem box_eq (a : α) : SRA.box a = SRA.j * a * SRA.j := rfl

/-- `□a ≤ a`. Two applications of `j_le_one`. -/
theorem box_le (a : α) : SRA.box a ≤ a := by
  change SRA.j * a * SRA.j ≤ a
  calc SRA.j * a * SRA.j
      ≤ 1 * a * 1 := mul_le_mul' (mul_le_mul' SRA.j_le_one le_rfl) SRA.j_le_one
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
          (mul_le_mul' SRA.j_le_one le_rfl)) le_rfl
    _ = SRA.j * a * b * SRA.j := by rw [one_mul]
    _ = SRA.j * (a * b) * SRA.j := by rw [mul_assoc SRA.j a b]

/-- `(□a)ᵒ = □(aᵒ)`. From `box_eq` and `j_converse`. -/
theorem box_converse (a : α) : (SRA.box a)ᵒ = SRA.box (aᵒ) := by
  change (SRA.j * a * SRA.j)ᵒ = SRA.j * aᵒ * SRA.j
  calc (SRA.j * a * SRA.j)ᵒ
      = (SRA.j)ᵒ * (SRA.j * a)ᵒ := IsInvolutiveQuantale.mul_converse _ _
    _ = (SRA.j)ᵒ * (aᵒ * (SRA.j)ᵒ) := by rw [IsInvolutiveQuantale.mul_converse]
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

/-- `□Δη = ⊥`. From `j_mul_varDiag_le_bot` and `Quantale.bot_mul` (the
quantale fact that `⊥` is a left annihilator, itself a consequence of
`sSup_mul_distrib` on the empty set). -/
theorem box_varDiag_eq_bot : SRA.box (SRA.varDiag : α) = ⊥ := by
  change SRA.j * SRA.varDiag * SRA.j = ⊥
  refine le_antisymm ?_ bot_le
  calc SRA.j * SRA.varDiag * SRA.j
      ≤ (⊥ : α) * SRA.j := mul_le_mul' SRA.j_mul_varDiag_le_bot le_rfl
    _ = ⊥ := Quantale.bot_mul

/-! #### Investigation: the dropped axiom `box_subst_le`

Old class field: `subst (box a) b ≤ box a`. In the new presentation, this
would read `subst (j * a * j) b ≤ j * a * j`. It does **not** derive from
any condition on `j` alone, and it does **not** hold in the intended
context-indexed model.

Attempted derivation from `subst j b ≤ j` (the natural "j is
substitution-closed" axiom): every route through `SRA.subst_mul_le` — which
is oplax, `subst (a * a') (b * b') ≤ subst a b * subst a' b'` — leaks the
middle `a` factor into a `subst a c` term for some `c ∈ {1, b}` that is
never bounded above by `a` (only below, via `subst_varDiag_right`
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

/-! ## Experiments — advisor's substitution-side suggestions

Three investigative results on the substitution side of `SRA`. NONE of
the three is added to the class: Experiment 1 confirms the class's
current field is the weaker of two candidate orthogonality forms;
Experiment 2 shows an advisor-suggested `subst j T = ⊥` axiom collapses
the theory; Experiment 3 records `∀ a, IsClosed (subst a j)` as a
candidate axiom with a positive term-model verification but no route
from the current axioms. -/

/-! ### Experiment 1 — meet form of the varDiag/j orthogonality

The class currently carries the multiplicative form
`SRA.j_mul_varDiag_le_bot : j * varDiag ≤ ⊥`. The advisor's proposal
was the meet form `varDiag ⊓ j ≤ ⊥`. Below we relate them. -/

/-- `j * varDiag ≤ varDiag ⊓ j`. Both components are one-liners from
the co-reflexivity axioms `j_le_one` and `varDiag_le_one`. Consequence
(next lemma): the meet form is at least as strong as the multiplicative
form. -/
theorem j_mul_varDiag_le_meet :
    SRA.j * (SRA.varDiag : α) ≤ SRA.varDiag ⊓ SRA.j := by
  refine le_inf ?_ ?_
  · calc SRA.j * SRA.varDiag
        ≤ 1 * SRA.varDiag := mul_le_mul' SRA.j_le_one le_rfl
      _ = SRA.varDiag := one_mul _
  · calc SRA.j * SRA.varDiag
        ≤ SRA.j * 1 := mul_le_mul' le_rfl varDiag_le_one
      _ = SRA.j := mul_one _

/-- The meet form implies the multiplicative form: `varDiag ⊓ j ≤ ⊥ →
j * varDiag ≤ ⊥`, via `j_mul_varDiag_le_meet`. -/
theorem j_mul_varDiag_le_bot_of_meet
    (h : (SRA.varDiag : α) ⊓ SRA.j ≤ ⊥) :
    SRA.j * (SRA.varDiag : α) ≤ ⊥ :=
  j_mul_varDiag_le_meet.trans h

/-! The converse implication `j * varDiag ≤ ⊥ → varDiag ⊓ j ≤ ⊥` does
NOT close from the current axioms. The natural route is

    varDiag ⊓ j  ≤  (varDiag ⊓ j) * (varDiag ⊓ j)  ≤  j * varDiag  ≤  ⊥,

where the last step is the mult-form hypothesis and the middle step is
projection twice via `mul_le_mul'` (`varDiag ⊓ j ≤ j` on the left,
`varDiag ⊓ j ≤ varDiag` on the right). The first step is
co-transitivity of the meet
`varDiag ⊓ j ≤ (varDiag ⊓ j) * (varDiag ⊓ j)`. The class supplies
`varDiag_le_mul_self` and `j_le_mul_self` in isolation, but neither
lifts through `⊓` — co-transitivity is not preserved by binary meets in
a general quantale (the counterexample is any `x` with `x ≤ x * x`
failing, e.g. `x = a ⊓ b` where `a`, `b` are individually co-transitive
but their meet is not).

**Recommendation.** Keep `SRA.j_mul_varDiag_le_bot` (the current field):
it is the weaker, more permissive assumption. Switching to the meet
form would strengthen the class without gaining a downstream lemma. -/

/-! ### Experiment 2 — `subst j T = ⊥` collapses the theory. -/

/-- The advisor's alternative suggestion `∀ T, subst j T = ⊥` forces
`j = ⊥`, whence `box a = j * a * j = ⊥` for every `a` — the whole modal
structure collapses. Two lines: instantiate at `T := varDiag` and apply
`subst_varDiag_right : subst a varDiag = a`. Recorded as a
hypothesis-carrying theorem — the hypothesis is NOT added as a class
axiom. -/
theorem j_eq_bot_of_subst_j_eq_bot
    (h : ∀ T : α, SRA.subst SRA.j T = ⊥) : (SRA.j : α) = ⊥ := by
  have := h SRA.varDiag
  rwa [SRA.subst_varDiag_right] at this

/-! ### Experiment 3 — `T[j]` closed.

Advisor's third suggestion: for every `a`, `subst a j` is a closed
relation, `IsClosed (subst a j)`. We state it as a bare `def`, note
that no route from the current axioms discharges it, argue in the
docstring that it cannot rescue the dropped `box_subst_le` (the latter
is false in the intended model whereas `SubstJClosed` is true there —
see `SynRel.substJClosed` in `Instances/FirstOrder/SRA.lean`), and
leave it here as a candidate axiom with recorded model justification. -/

/-- Candidate axiom: "substitution by `j` yields a closed relation."
Stated as a top-level `def`, NOT added to the `SRA` class. -/
def SubstJClosed (α : Type*) [Monoid α] [CompleteLattice α]
    [IsQuantale α] [IsInvolutiveQuantale α] [SRA α] : Prop :=
  ∀ a : α, SRA.IsClosed (SRA.subst a SRA.j)

/-! **Why `SubstJClosed` is not derivable from the current axioms.**
The `SRA` fields governing `subst`
(`subst_mono_right`, `subst_mul_le`, `subst_converse`,
`subst_sSup_left`, `subst_varDiag_left`, `subst_varDiag_right`,
`subst_assoc`, `subst_scr_le`) do not mention `j`. The `j` fields
(`j_le_one`, `j_converse_le`, `j_le_mul_self`, `j_mul_varDiag_le_bot`)
constrain `j` in isolation, on the *multiplicative* side. To conclude
`subst a j ≤ j * (subst a j) * j` one needs a bridge between the
substitution operator and `j` on the input side — a fact the current
axioms simply do not carry.

**Why `SubstJClosed` cannot rescue the dropped `box_subst_le`.**
The dropped law `subst (box a) b ≤ box a` was shown earlier to be
FALSE in the context-indexed term model of `Instances/FirstOrder`
(counterexample: `a.rel Γ t s := Nonempty Γ`, `Θ := Empty`,
`b := ⊤`). Below, `SynRel.substJClosed` shows `SubstJClosed` is TRUE
in that same model. A putative derivation
`SubstJClosed → box_subst_le` would then instantiate at the model to
give `True → False = False`; but a derivation is a theorem, and
theorems hold in every model of their hypotheses. Contradiction.
There is no such derivation, and no point searching. -/

/-! ### Experiment 3′ — `j[T] = j` (advisor's corrected form). -/

/-- Candidate axiom: substitution by `j` in the first argument is
absorbing on `j`, i.e., `∀ T, j[T] = j`. Stated as a top-level `def`
alongside `SubstJClosed`; NOT added to the `SRA` class.

This is the advisor's corrected replacement for the earlier
`∀ T, j[T] = ⊥` proposal (refuted by `j_eq_bot_of_subst_j_eq_bot`:
that form collapses `j` to `⊥`). The corrected form is *not* similarly
refuted — it is consistent with the current axioms and holds in the
intended context-indexed term model.

**Model justification (see `SynRel.substJEqJ` in
`Instances/FirstOrder/SRA.lean`).** In that model, `j` is the identity
on weakened closed terms. The `⊆` direction uses `Tm.subst_close`:
substitution acts trivially on a weakened closed term, so both endpoints
`t.subst τ`, `s.subst σ` of a `subst j T`-witness collapse to the same
weakened closed term. The `⊇` direction is even simpler and — crucially
— holds for **every** `T`, including `T = ⊥`: take source context
`Γ := Empty`, whence the pointwise clause `∀ x : Empty, T.rel Δ (τ x)
(σ x)` is vacuous. It is precisely this vacuous-source-context route
that made the earlier `j[T] = ⊥` form collapse (`j ≤ j[⊥]` still holds
via `Γ := Empty`, forcing `j ≤ ⊥` under the old proposal). -/
def SubstJEqJ (α : Type*) [Monoid α] [CompleteLattice α]
    [IsQuantale α] [IsInvolutiveQuantale α] [SRA α] : Prop :=
  ∀ T : α, SRA.subst SRA.j T = SRA.j

/-! **Why `SubstJEqJ` is not derivable from the current axioms.** Same
structural obstruction as `SubstJClosed`: the `subst` fields
(`subst_mono_right`, `subst_mul_le`, `subst_converse`,
`subst_sSup_left`, `subst_varDiag_left`, `subst_varDiag_right`,
`subst_assoc`, `subst_scr_le`) do not mention `j`, and the `j` fields
constrain `j` only on the *multiplicative* side. The only equation the
current axioms give for `SRA.subst j T` is at the single point
`T := varDiag`, via `subst_varDiag_right : subst j varDiag = j`. No
combination pins `subst j T` for a second value of `T`, let alone for
all `T`.

**Consumption in the current development.** Nothing in `Structure/`,
`Confluence/`, or `Instances/` currently consumes `SubstJEqJ`. It is
recorded here as a *candidate* — a hypothesis future work may or may
not need — with the term-model justification above; it is not fed to
the `SRA` class, and there is no downstream lemma stated in terms of
it yet. -/

/-! ### Experiment 4 — meet vs. composition of co-equivalences.

In the allegory of relations, any two coreflexives `R, S ≤ 1` satisfy
`R ⊓ S = R * S`. The standard proof uses the modular law
`(P * Q) ⊓ R ≤ P * (Q ⊓ Pᵒ * R)`:
    `R ⊓ S = (R * 1) ⊓ S ≤ R * (1 ⊓ Rᵒ * S) ≤ R * S`.
The bare involutive quantale here has no modular law. Below we take the
six co-equivalence hypotheses as explicit arguments and record which
half closes.

The `R * S ≤ R ⊓ S` direction closes from co-reflexivity alone
(`R ≤ 1`, `S ≤ 1`); the other direction is left as an
`example` that we do NOT expect to close — the residual is documented
below. -/

omit [IsInvolutiveQuantale α] [SRA α] in
/-- Half 1 of the meet-vs-composition question, unconditional in the
symmetry and co-transitivity hypotheses: for coreflexives `R, S ≤ 1`,
`R * S ≤ R ⊓ S`. `R * S ≤ R * 1 = R` and `R * S ≤ 1 * S = S`. -/
theorem mul_le_meet_of_coreflexive {R S : α} (hR1 : R ≤ 1) (hS1 : S ≤ 1) :
    R * S ≤ R ⊓ S := by
  refine le_inf ?_ ?_
  · calc R * S ≤ R * 1 := mul_le_mul' le_rfl hS1
      _ = R := mul_one _
  · calc R * S ≤ 1 * S := mul_le_mul' hR1 le_rfl
      _ = S := one_mul _

/-! Attempted converse: `R ⊓ S ≤ R * S` for co-equivalences
`R, S ≤ 1` with `Rᵒ ≤ R`, `Sᵒ ≤ S`, `R ≤ R * R`, `S ≤ S * S`.

Available consequences of the six hypotheses:
* `R = Rᵒ` and `S = Sᵒ` (one-line involutivity argument, cf.
  `varDiag_converse`);
* `R * R = R` and `S * S = S` (co-transitivity `R ≤ R * R` combined with
  `R * R ≤ 1 * R = R` from co-reflexivity).

Attempts and where each stalls:

1.  `R ⊓ S ≤ R = R * R = R * (something)` — needs the "something" to sit
    below `S`, which the hypotheses do not deliver.
2.  Multiply on the left by `R`:
      `R * (R ⊓ S) ≤ R * R ⊓ R * S = R ⊓ R * S`
    would require distributivity of `*` over `⊓`, and composition in a
    general quantale distributes over `sSup` (joins), NOT over `sInf`
    (meets). So the middle equality does not close, and `R * (R ⊓ S)`
    is only sandwiched between `R * S` (below) and `R` (below) — no
    route up to `R ⊓ S`.
3.  Co-transitivity applied to the meet — `R ⊓ S ≤ (R ⊓ S) * (R ⊓ S)`
    would close from `mul_le_mul'` and inf-projections, but this
    lemma requires co-transitivity of `R ⊓ S` itself. As Experiment 1
    already documents (`j_mul_varDiag_le_bot_of_meet` block), binary
    meets do not preserve co-transitivity in a general quantale.
4.  Symmetry rewrite `R ⊓ S = Rᵒ ⊓ Sᵒ`: transposes the problem to
    `Rᵒ ⊓ Sᵒ ≤ Rᵒ * Sᵒ = (S * R)ᵒ`, i.e., `(R ⊓ S)ᵒ ≤ (S * R)ᵒ`, which
    is `R ⊓ S ≤ S * R` — a symmetric rewrite of the same open goal.

Unused hypotheses in the attempts above: **all six** are used to
derive `R = Rᵒ`, `R * R = R`, and their `S`-analogues, but no
combination of the derived facts closes the residual — the exact goal
we cannot discharge is

    `R ⊓ S ≤ R * S`

with all six hypotheses on the context. The obstruction is the missing
modular law; the bare involutive quantale is genuinely too weak.

Recorded as commented `example` rather than a `theorem` (to avoid a
`sorry`) so that a future reader can pick up where we stopped:

```
example {R S : α}
    (hR1 : R ≤ 1) (hRc : Rᵒ ≤ R) (hRt : R ≤ R * R)
    (hS1 : S ≤ 1) (hSc : Sᵒ ≤ S) (hSt : S ≤ S * S) :
    R ⊓ S ≤ R * S := by
  sorry
```
-/

end SRA
