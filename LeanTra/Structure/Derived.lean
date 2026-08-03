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
* Modalities on the *primitive* `SRA.box`. The advisor's axioms
  (`SRA.box_le`, `SRA.box_box`, `SRA.box_mono`, the two absorption laws,
  `SRA.box_mul_box_le`, `SRA.box_varDiag_eq_bot`, `SRA.box_subst_le`,
  plus the two co-equivalence conditions on `□1`) are used directly by
  their `SRA.`-qualified names — no aliases.

  DERIVED from those axioms alone:
    - the diamond `dia a := sSup {x | box x ≤ a}` as the pointwise
      right-adjoint candidate;
    - `dia_mono`;
    - the easy half of the adjunction, `le_dia_of_box_le`.

  CONDITIONAL on `hjoin`, the hypothesis that `□` preserves arbitrary
  joins (`∀ s, □(sSup s) = sSup (□ '' s)`) — a fact not derivable from
  the current axioms, threaded as an explicit argument:
    - the full adjunction `box_le_iff`;
    - the transfer lemma `box_lfp` (the paper's Lemma 16).

  LOST relative to the pre-migration file:
    - `box_subst` was an equality; only the `≤` half survives, as the
      class field `SRA.box_subst_le`;
    - `box_mul_le` had direction `□(a * b) ≤ □a * □b`; the new lax axiom
      `SRA.box_mul_box_le` has the opposite direction `□a * □b ≤ □(a * b)`.
  Neither loss has a consumer in the current codebase.

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

`□` is a *primitive* field of `SRA` (see the design note in
`Structure/SRA.lean`) with exactly the axioms the advisor supplied. The
source's structural corollaries — the identity `□a = e * a * e`, symmetry
`(□a)ᵒ = □(aᵒ)`, join-preservation `□(sSup s) = sSup (□ '' s)` — are NOT
derivable from those axioms and are NOT re-derived here. In particular,
the identity fails in the context-indexed term model formalised in
`Instances/FirstOrder` (see the counterexample in `Structure/SRA.lean`'s
design note), and so does the join-preservation law that would follow
from it.

What this section develops from the axioms alone:

* the diamond `dia a := sSup {x | box x ≤ a}` as the pointwise right
  adjoint candidate, together with monotonicity `dia_mono`;
* the easy half of the adjunction `le_dia_of_box_le`, which is a one-line
  `le_sSup`.

What it develops *conditional* on `□` preserving arbitrary joins — a
hypothesis threaded through as an explicit argument, since it is not an
axiom of `SRA`:

* the full adjunction `box_le_iff` (both directions);
* the fixed-point transfer lemma `box_lfp` (the paper's Lemma 16).

Both would be immediate consequences of the source identity `□a = e * a * e`
once that identity is available in a stronger set-up; here we make the
dependence explicit rather than assume it. -/

/-! #### Diamond as the right adjoint candidate -/

/-- Diamond `♦a`: the pointwise right-adjoint candidate for `□`,
`sSup {x | □x ≤ a}`. Same construction pattern as `substResid`. Whether
this actually *is* the right adjoint depends on `□` preserving arbitrary
joins — a fact not derivable from the current axioms; see
`box_le_iff` below, which takes join-preservation as a hypothesis. -/
def dia (a : α) : α := sSup {x | SRA.box x ≤ a}

/-- `♦` is monotone. -/
theorem dia_mono ⦃a a' : α⦄ (h : a ≤ a') : dia a ≤ dia a' :=
  sSup_le_sSup fun _ hx => le_trans hx h

/-- Easy half of the `□ ⊣ ♦` adjunction: `□a ≤ b → a ≤ ♦b`. One line —
`a` is in the defining set of `♦b`, so `a ≤ sSup {…}`. Unconditional. -/
theorem le_dia_of_box_le {a b : α} (h : SRA.box a ≤ b) : a ≤ dia b :=
  le_sSup h

/-- The full `□ ⊣ ♦` adjunction. Hypothesis-carrying: the backward
direction pushes `□` through the defining supremum of `♦b` and thus
depends on `□` preserving arbitrary joins (`hjoin`). This is the
statement the advisor's derivation `□a = e * a * e` would yield
unconditionally once available; here we carry `hjoin` as an explicit
argument because it is not derivable from the current axioms — see the
design note in `Structure/SRA.lean`. -/
theorem box_le_iff
    (hjoin : ∀ s : Set α, SRA.box (sSup s) = sSup (SRA.box '' s))
    {a b : α} : SRA.box a ≤ b ↔ a ≤ dia b := by
  refine ⟨le_dia_of_box_le, fun h => ?_⟩
  calc SRA.box a
      ≤ SRA.box (dia b) := SRA.box_mono h
    _ = sSup (SRA.box '' {x | SRA.box x ≤ b}) := hjoin _
    _ ≤ b := by
        refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hx

/-! ### Closed relations -/

/-- Closedness: a relation `a` is closed when it refines its own `box`. -/
def IsClosed (a : α) : Prop := a ≤ SRA.box a

/-- `a` is closed iff `□a = a`. -/
theorem isClosed_iff {a : α} : IsClosed a ↔ SRA.box a = a :=
  ⟨fun h => le_antisymm (SRA.box_le a) h, fun h => h.ge⟩

/-- `□a` is always closed. -/
theorem box_isClosed (a : α) : IsClosed (SRA.box a) := (SRA.box_box a).ge

/-- `⊥` is closed. -/
theorem isClosed_bot : IsClosed (⊥ : α) := bot_le

/-! ### Closed monotone functions and the transfer lemma -/

/-- A monotone `F` is closed when `□ ∘ F ≤ F ∘ □` pointwise. -/
def IsClosedFun (F : α →o α) : Prop := ∀ x, SRA.box (F x) ≤ F (SRA.box x)

/-- Composition `box ∘ F` bundled as an `OrderHom`. -/
def boxComp (F : α →o α) : α →o α where
  toFun x := SRA.box (F x)
  monotone' _ _ h := SRA.box_mono (F.mono h)

/-- Transfer lemma (the paper's Lemma 16): for a closed monotone `F`, `□`
commutes with the least fixed point — `□(μF) = μ(□∘F)`. Proof rides on
`box_box`, `box_mono`, `box_le` and the adjunction `box_le_iff`;
threading the same `hjoin` hypothesis through, since the adjunction needs
`□` to preserve arbitrary joins and that fact is not derivable from the
current axioms — see the design note in `Structure/SRA.lean`. This is
the statement the advisor's derivation would yield unconditionally once
`box_eq` (and hence `hjoin`) is available. -/
theorem box_lfp
    (hjoin : ∀ s : Set α, SRA.box (sSup s) = sSup (SRA.box '' s))
    {F : α →o α} (hF : IsClosedFun F) :
    SRA.box F.lfp = (boxComp F).lfp := by
  refine le_antisymm ?_ ?_
  · refine (box_le_iff hjoin).mpr ?_
    refine F.lfp_le ?_
    refine (box_le_iff hjoin).mp ?_
    calc SRA.box (F (dia (boxComp F).lfp))
        = SRA.box (SRA.box (F (dia (boxComp F).lfp))) := (SRA.box_box _).symm
      _ ≤ SRA.box (F (SRA.box (dia (boxComp F).lfp))) := SRA.box_mono (hF _)
      _ ≤ SRA.box (F (boxComp F).lfp) :=
          SRA.box_mono (F.mono ((box_le_iff hjoin).mpr le_rfl))
      _ = (boxComp F).lfp := (boxComp F).map_lfp
  · refine (boxComp F).lfp_le ?_
    change SRA.box (F (SRA.box F.lfp)) ≤ SRA.box F.lfp
    calc SRA.box (F (SRA.box F.lfp))
        ≤ SRA.box (F F.lfp) := SRA.box_mono (F.mono (SRA.box_le _))
      _ = SRA.box F.lfp := by rw [F.map_lfp]

-- Sanity: every surviving result depends on only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`.
#print axioms SRA.isClosed_bot
#print axioms SRA.box_isClosed
#print axioms SRA.le_dia_of_box_le
#print axioms SRA.box_le_iff
#print axioms SRA.box_lfp

-- The corollary `IsClosed F.lfp` under `IsClosedFun F` is NOT derivable.
-- Counterexample in the `Toy` SRA (`α := Prop`, `box _ := ⊥` in the new
-- axiomatisation): take `F := ⟨fun _ => ⊤, _⟩`, constant top. Then
-- `IsClosedFun F` holds vacuously (`box (F x) = ⊥ ≤ ⊤ = F (box x)`),
-- and `F.lfp = ⊤`, but `box F.lfp = ⊥`, so `F.lfp ≤ box F.lfp` fails.
-- The missing hypothesis is either the reverse naturality
-- `F (box x) ≤ box (F x)` (giving equality `box ∘ F = F ∘ box`, so `F`
-- would preserve the image of `box`) or "F preserves closed elements"
-- (`IsClosed x → IsClosed (F x)`) — the lax naturality alone is not enough.

end SRA
