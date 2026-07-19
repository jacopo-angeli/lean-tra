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
* Basic laws of the derived operation `·̂`: monotonicity, restatement of the
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
* Modalities `box a := a[⊥]` and `dia a := ⊥ » a` (the source's `♦a := a » ⊥`
  is a confirmed typo — the right adjoint of `□` is `⊥ » ·`), together with
  the laws
  that derive from the current axioms: `box_le`, `box_converse`, `box_mono`,
  `box_subst`, `dia_mono`, the adjunction `box_le_iff : □a ≤ b ↔ a ≤ ♦b`,
  and the oplax `box_mul_le`. The equality `box_mul : □(a * b) = □a * □b`
  does NOT derive here — only the `≤` direction — see comment.
* Closed relations: `IsClosed a := a ≤ box a`, characterisation
  `isClosed_iff`, and the fact that `box a` and `⊥` are always closed.
* Transfer to fixed points: `IsClosedFun F := ∀ x, box (F x) ≤ F (box x)`
  for a monotone `F`, and `box_lfp : box F.lfp = (boxComp F).lfp` — `box`
  commutes with least fixed points of closed functions.

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

/-- `ẽ 1 ≤ 1`: the strict compatible refinement is oplax on the unit. -/
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

/-- `·̂` is monotone. -/
theorem cr_mono ⦃a b : α⦄ (h : a ≤ b) : cr a ≤ cr b :=
  sup_le_sup_left (SRA.scr_mono h) _

/-- Fixed-point law for `·̂`: `1̂ = 1`. -/
@[simp]
theorem cr_one : cr (1 : α) = 1 := SRA.varDiag_sup_scr_one_eq

/-- Structural induction: `1` is the least pre-fixed point of `·̂`. -/
theorem one_le_of_cr_le ⦃a : α⦄ (h : cr a ≤ a) : 1 ≤ a :=
  SRA.one_le_of_scr_sup_le h

/-! ### Orthogonality on the right -/

/-- Symmetric orthogonality: `ẽa * Δη ≤ ⊥`, derived from the axiomatic
left-orthogonality via converse. -/
theorem scr_mul_varDiag_le_bot (a : α) : SRA.scr a * SRA.varDiag ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_le_converse_iff,
      IsInvolutiveQuantale.converse_bot,
      IsInvolutiveQuantale.mul_converse,
      ← SRA.scr_converse, varDiag_converse]
  exact SRA.varDiag_mul_scr_le_bot _

/-! ### Multiplicativity of Δη and `·̂` -/

/-- `Δη * Δη = Δη`: the variable co-equivalence is idempotent under
composition. -/
@[simp]
theorem varDiag_mul_self : (SRA.varDiag : α) * SRA.varDiag = SRA.varDiag := by
  refine le_antisymm ?_ SRA.varDiag_le_mul_self
  calc (SRA.varDiag : α) * SRA.varDiag
      ≤ 1 * SRA.varDiag := mul_le_mul' varDiag_le_one le_rfl
    _ = SRA.varDiag := one_mul _

/-- `·̂` distributes over composition: `â * b̂ = (a * b)̂`. -/
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

/-- `·̂` commutes with converse: `(â)ᵒ = (aᵒ)̂`. -/
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
induction on `·̂`. -/
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

Box `□a := a[⊥]` and diamond `♦a := ⊥ » a`. The definition of `♦` reads off
the adjunction `·[b] ⊣ b » ·` at `b = ⊥`: the right adjoint of `□ = ·[⊥]` is
`⊥ » ·`. -/

/-- Box modality: `□a := a[⊥]`. -/
def box (a : α) : α := SRA.subst a ⊥

/-- Diamond modality: `♦a := ⊥ » a`. The source defines `♦a := a » ⊥` — a
typo confirmed by the author. The right adjoint of `□ = ·[⊥]` is `⊥ » ·`,
read off `·[b] ⊣ b » ·` at `b = ⊥`; that is why `box_le_iff` below is a
one-line instance of `subst_le_iff`. -/
def dia (a : α) : α := substResid ⊥ a

/-- Closed relations refine their argument: `□a ≤ a`. -/
theorem box_le (a : α) : box a ≤ a := by
  unfold box
  calc SRA.subst a ⊥
      ≤ SRA.subst a SRA.varDiag := SRA.subst_mono_right bot_le
    _ = a := SRA.subst_varDiag_right a

/-- `□` commutes with converse: `(□a)ᵒ = □(aᵒ)`. -/
theorem box_converse (a : α) : (box a)ᵒ = box (aᵒ) := by
  unfold box
  rw [SRA.subst_converse, IsInvolutiveQuantale.converse_bot]

/-- `□` is monotone. -/
theorem box_mono ⦃a a' : α⦄ (h : a ≤ a') : box a ≤ box a' :=
  subst_mono_left h

/-- Substitution is idempotent on closed relations: `(□a)[b] = □a`. -/
theorem box_subst (a b : α) : SRA.subst (box a) b = box a := by
  unfold box
  rw [SRA.subst_assoc, subst_bot_left]

/-- `□` is idempotent: `□(□a) = □a`. Direct corollary of `box_subst` at
`b := ⊥`. -/
theorem box_box (a : α) : box (box a) = box a := box_subst a ⊥

/-- `□` collapses the variable co-equivalence: `□Δη = ⊥`. Direct corollary
of `subst_varDiag_left` at `a := ⊥`. -/
theorem box_varDiag : box (SRA.varDiag : α) = ⊥ := SRA.subst_varDiag_left ⊥

/-- `♦` is monotone. -/
theorem dia_mono ⦃a a' : α⦄ (h : a ≤ a') : dia a ≤ dia a' :=
  sSup_le_sSup fun _ hx => le_trans hx h

/-- Adjunction: `□ ⊣ ♦`. Direct instance of `subst_le_iff` at `b = ⊥`. -/
theorem box_le_iff {a b : α} : box a ≤ b ↔ a ≤ dia b := subst_le_iff

/-- Oplax multiplicativity: `□(a * b) ≤ □a * □b`. -/
theorem box_mul_le (a b : α) : box (a * b) ≤ box a * box b := by
  have h : SRA.subst (a * b) (⊥ * ⊥) ≤ SRA.subst a ⊥ * SRA.subst b ⊥ :=
    SRA.subst_mul_le a b ⊥ ⊥
  rwa [Quantale.bot_mul] at h

-- The equality `box_mul : □(a * b) = □a * □b` — asserted by the source —
-- is NOT derivable from the current axioms. Only the oplax direction above
-- follows from `subst_mul_le`; the reverse would need a lax-bimorphism
-- axiom on substitution that we do not have.

/-! ### Closed relations -/

/-- Closedness: a relation `a` is closed when it refines its own `box`. -/
def IsClosed (a : α) : Prop := a ≤ box a

/-- `a` is closed iff `□a = a`. -/
theorem isClosed_iff {a : α} : IsClosed a ↔ box a = a :=
  ⟨fun h => le_antisymm (box_le a) h, fun h => h.ge⟩

/-- `□a` is always closed. -/
theorem box_isClosed (a : α) : IsClosed (box a) := (box_box a).ge

/-- `⊥` is closed. -/
theorem isClosed_bot : IsClosed (⊥ : α) := bot_le

/-! ### Closed monotone functions and the transfer lemma -/

/-- A monotone `F` is closed when `□ ∘ F ≤ F ∘ □` pointwise. -/
def IsClosedFun (F : α →o α) : Prop := ∀ x, box (F x) ≤ F (box x)

/-- Composition `box ∘ F` bundled as an `OrderHom`. -/
def boxComp (F : α →o α) : α →o α where
  toFun x := box (F x)
  monotone' _ _ h := box_mono (F.mono h)

/-- Transfer lemma: for a closed monotone `F`, `□` commutes with the least
fixed point — `□(μF) = μ(□∘F)`. -/
theorem box_lfp {F : α →o α} (hF : IsClosedFun F) :
    box F.lfp = (boxComp F).lfp := by
  refine le_antisymm ?_ ?_
  · refine box_le_iff.mpr ?_
    refine F.lfp_le ?_
    refine box_le_iff.mp ?_
    calc box (F (dia (boxComp F).lfp))
        = box (box (F (dia (boxComp F).lfp))) := (box_box _).symm
      _ ≤ box (F (box (dia (boxComp F).lfp))) := box_mono (hF _)
      _ ≤ box (F (boxComp F).lfp) :=
          box_mono (F.mono (box_le_iff.mpr le_rfl))
      _ = (boxComp F).lfp := (boxComp F).map_lfp
  · refine (boxComp F).lfp_le ?_
    change box (F (box F.lfp)) ≤ box F.lfp
    calc box (F (box F.lfp))
        ≤ box (F F.lfp) := box_mono (F.mono (box_le _))
      _ = box F.lfp := by rw [F.map_lfp]

-- The corollary `IsClosed F.lfp` under `IsClosedFun F` is NOT derivable.
-- Counterexample in the `Toy` SRA (`α := Prop`, `subst a b := a ∧ b`, so
-- `box a = ⊥` on every `a`): take `F := ⟨fun _ => ⊤, _⟩`, constant top.
-- Then `IsClosedFun F` holds vacuously (`box (F x) = ⊥ ≤ ⊤ = F (box x)`),
-- and `F.lfp = ⊤`, but `box F.lfp = ⊥`, so `F.lfp ≤ box F.lfp` fails.
-- The missing hypothesis is either the reverse naturality
-- `F (box x) ≤ box (F x)` (giving equality `box ∘ F = F ∘ box`, so `F`
-- would preserve the image of `box`) or "F preserves closed elements"
-- (`IsClosed x → IsClosed (F x)`) — the lax naturality alone is not enough.

end SRA

/-! ## Notation

Scoped postfix `ᴴ` for the Howe extension, and infix `»` for the
substitution residual. -/

@[inherit_doc SRA.substResid]
scoped[SRA] infixr:60 " » " => SRA.substResid

@[inherit_doc SRA.howe]
-- Precedence pitfall (same as `ˆ`): `ẽaᴴ` parses as `ẽ(aᴴ)` since postfix
-- `ᴴ` (max) binds before prefix `ẽ` (also max). For the reading `(ẽa)ᴴ`,
-- always write the explicit parens.
scoped[SRA] postfix:max "ᴴ" => SRA.howe
