/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
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

## Status — open items

A running list of substitution-side questions that survived the advisor's
iteration but have NOT been folded into the class or the derived layer.
Full prose per item lives in `docs/modality-experiments.md`.

* `SubstJEqJ` — `∀ T, subst j T = j` (`j[T] = j`). Candidate predicate
  (`SRA.SubstJEqJ`, this file); true in the term model
  (`LeanTra.Instances.FirstOrder.SynRel.substJEqJ`); not derivable; no
  consumer yet. The advisor's earlier `∀ T, subst j T = ⊥` proposal
  was refuted (it forces `j = ⊥`; see
  `SRA.j_eq_bot_of_subst_j_eq_bot`).
* `R ⊓ S ≤ R * S` for co-equivalences — OPEN. The easy direction
  `R * S ≤ R ⊓ S` is `SRA.mul_le_meet_of_coreflexive` in this file;
  the reverse is not proved. No separating model has been found, so
  the status is "not proved", not "not derivable".

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

/-! ### Derived ex-axioms -/

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

/-- `1[1] = 1`: substituting the identity into the identity is the identity. -/
theorem subst_one_one : SRA.subst (1 : α) 1 = 1 := by
  refine le_antisymm ?_ ?_
  · refine subst_le_iff.mpr ?_
    refine one_le_of_cr_le ?_
    refine sup_le ?_ ?_
    · exact subst_le_iff.mp (by rw [SRA.subst_varDiag_left])
    · refine subst_le_iff.mp ?_
      calc SRA.subst (SRA.scr (SRA.substResid (1 : α) 1)) 1
          ≤ SRA.scr (SRA.subst (SRA.substResid (1 : α) 1) 1) := SRA.subst_scr_le _ _
        _ ≤ SRA.scr 1 := SRA.scr_mono (subst_le_iff.mpr le_rfl)
        _ ≤ 1 := scr_one_le
  · calc (1 : α)
        = SRA.subst SRA.varDiag 1 := (SRA.subst_varDiag_left 1).symm
      _ ≤ SRA.subst 1 1 := subst_mono_left varDiag_le_one

/-! ## Experiments — advisor's substitution-side suggestions

Investigative results whose PROSE lives in `docs/modality-experiments.md`.
Below, each experiment is a one-line pointer plus whatever Lean
declarations it produced. NONE of the candidate predicates is added to
the `SRA` class. -/

/-! ### Experiment 1 — meet form of the varDiag/j orthogonality.
See `docs/modality-experiments.md#experiment-1`. -/

/-- `j * varDiag ≤ varDiag ⊓ j` from the two co-reflexivity axioms. -/
theorem j_mul_varDiag_le_meet :
    SRA.j * (SRA.varDiag : α) ≤ SRA.varDiag ⊓ SRA.j := by
  refine le_inf ?_ ?_
  · calc SRA.j * SRA.varDiag
        ≤ 1 * SRA.varDiag := mul_le_mul' SRA.j_le_one le_rfl
      _ = SRA.varDiag := one_mul _
  · calc SRA.j * SRA.varDiag
        ≤ SRA.j * 1 := mul_le_mul' le_rfl varDiag_le_one
      _ = SRA.j := mul_one _

/-- Meet form implies multiplicative form: `varDiag ⊓ j ≤ ⊥` gives
`j * varDiag ≤ ⊥`. -/
theorem j_mul_varDiag_le_bot_of_meet
    (h : (SRA.varDiag : α) ⊓ SRA.j ≤ ⊥) :
    SRA.j * (SRA.varDiag : α) ≤ ⊥ :=
  j_mul_varDiag_le_meet.trans h

/-! ### Experiment 2 — `subst j T = ⊥` collapses the theory.
See `docs/modality-experiments.md#experiment-2`. -/

/-- If `∀ T, subst j T = ⊥` then `j = ⊥`: instantiate at
`T := varDiag` and apply `subst_varDiag_right`. Hypothesis-carrying
theorem, NOT a class axiom. -/
theorem j_eq_bot_of_subst_j_eq_bot
    (h : ∀ T : α, SRA.subst SRA.j T = ⊥) : (SRA.j : α) = ⊥ := by
  have := h SRA.varDiag
  rwa [SRA.subst_varDiag_right] at this

/-! ### Experiment 3′ — `j[T] = j` (`SubstJEqJ`, advisor's corrected form).
See `docs/modality-experiments.md#experiment-3-1`; term-model
verification in `LeanTra.Instances.FirstOrder.SynRel.substJEqJ`. -/

/-- Candidate axiom: `∀ T, j[T] = j`. Advisor's corrected replacement
for the earlier `∀ T, j[T] = ⊥` (refuted by
`j_eq_bot_of_subst_j_eq_bot`). Top-level `def`, NOT a class field. Not
derivable; true in the term model. -/
def SubstJEqJ (α : Type*) [Monoid α] [CompleteLattice α]
    [IsQuantale α] [IsInvolutiveQuantale α] [SRA α] : Prop :=
  ∀ T : α, SRA.subst SRA.j T = SRA.j

/-! ### Experiment 4 — meet vs. composition of co-equivalences.
See `docs/modality-experiments.md#experiment-4`. Only the easy
half `R * S ≤ R ⊓ S` closes below; the converse `R ⊓ S ≤ R * S` is
open (not proved — no separating model). -/

omit [IsInvolutiveQuantale α] [SRA α] in
/-- Easy half of the coreflexive meet-vs-composition question:
`R * S ≤ R ⊓ S` from `R, S ≤ 1` alone. -/
theorem mul_le_meet_of_coreflexive {R S : α} (hR1 : R ≤ 1) (hS1 : S ≤ 1) :
    R * S ≤ R ⊓ S := by
  refine le_inf ?_ ?_
  · calc R * S ≤ R * 1 := mul_le_mul' le_rfl hS1
      _ = R := mul_one _
  · calc R * S ≤ 1 * S := mul_le_mul' hR1 le_rfl
      _ = S := one_mul _

end SRA
