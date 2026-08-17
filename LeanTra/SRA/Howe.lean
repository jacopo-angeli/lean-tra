/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
public import Mathlib.Order.FixedPoints

/-!
# The Howe extension and its op-Howe mirror

The Howe extension `aᴴ` of a relation `a`: the least solution of
`x = ⌃x * a`, where `⌃·` is the compatible refinement. Read relationally,
`aᴴ` relates two terms when the first can be refined, one layer of
structure at a time, into a term that `a` relates to the second — the
congruence-like closure that makes coinductive relations compatible with
term formation.

The construction needs nothing beyond the `SRA` axioms. `⌃·` is monotone,
so `x ↦ ⌃x * a` is monotone and Knaster–Tarski gives the least fixed
point; `OrderHom.lfp` supplies both the characteristic equation and the
induction principle.

## Uniqueness

The solution is not merely least, it is unique: any `b` with `b = ⌃b * a`
equals `aᴴ` (`howe_unique`, `howe_eq_of_fixpoint`). The extra inequality comes
from the left residual of composition, which the quantale supplies and
which the least-fixed-point property alone does not give.

## The op-Howe mirror

Converse turns `x = ⌃x * a` into the dual equation `x = a * ⌃x`, so the
converse of a Howe extension is not itself a Howe extension. The dual is
built here as `opHowe`, by the same recursor-plus-Knaster–Tarski scheme
and with the same uniqueness argument, the right residual `⇨ᵣ` replacing
the left one. `howe_converse` relates the two: `(aᴴ)ᵒ = (aᵒ)§`. It is
what lets the confluence development move between a parallel reduction
and its converse.

## Closedness

`substResid b c := sSup {a | a⟦b⟧ ≤ c}`, written `b » c` in the thesis
text, is the right adjoint of `·⟦b⟧`. Since substitution preserves
arbitrary joins in its first argument, the Adjoint Functor Theorem
applies and the join of the candidate set is itself a candidate; the
adjunction `subst_le_iff : a⟦b⟧ ≤ c ↔ a ≤ b » c` follows. This is what
makes the substitution monoid closed, which the reference asks for as an
assumption.

## References

* Douglas J. Howe. *Proving congruence of bisimulation in functional
  programming languages.* Information and Computation, 1996.
* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/


@[expose] public section

open scoped IsInvolutiveQuantale Quantale

namespace SRA

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [SRA α]



/-! ### Definition and fixed-point interface

`howe` is the least fixed point of the recursor, so its characteristic
equation and its induction principle are `map_lfp` and `lfp_le` read
through the definition. Everything below follows from these two. -/

/-- The Howe recursor: `x ↦ ⌃x * a`, bundled as an `OrderHom` so its least
fixed point can be taken via `OrderHom.lfp`. Internal helper for `howe`. -/
def howeRecursor (a : α) : α →o α where
  toFun x := cr x * a
  monotone' _ _ h := mul_le_mul_left (cr_monotonicity h) a

/-- Howe extension `·ᴴ`: the unique solution of `x = ⌃x * a` (see
`howe_unique`). Constructed as the least fixed point via Knaster–Tarski;
uniqueness — proved below via residuals — turns "the least solution" into
"the only solution". -/
def howe (a : α) : α := (howeRecursor a).lfp

/-- Fixed-point law: `aᴴ` satisfies `aᴴ = ⌃aᴴ * a`. -/
theorem howe_fixpoint (a : α) : howe a = cr (howe a) * a := ((howeRecursor a).map_lfp).symm

/-- Fixed-point induction: `aᴴ` is below every pre-fixed point of the Howe
recursion. -/
theorem howe_induction ⦃a x : α⦄ (h : cr x * a ≤ x) : howe a ≤ x := (howeRecursor a).lfp_le h



/-! ### Uniqueness

The fixed point is not merely least, it is the only one. The extra
inequality comes from the left residual of composition: residuating one
solution against the other turns the two fixed-point equations into a
statement about `Δ`, which structural induction on `⌃·` then discharges.
This is the one place in the file where the quantale structure is used
beyond monotonicity. -/

/-- One direction of uniqueness: any two solutions of `x = ⌃x * a` are
mutually below each other. Argument via the left residual `⇨ₗ` and structural
induction on `⌃·`. -/
private theorem howe_solution_le {a b c : α}
    (hb : b = cr b * a) (hc : c = cr c * a) : b ≤ c := by
  rw [show b = 1 * b from (one_mul b).symm]
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine one_le_of_cr_le ?_
  refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
  calc cr (b ⇨ₗ c) * b
      = cr (b ⇨ₗ c) * (cr b * a) := by rw [← hb]
    _ = cr (b ⇨ₗ c) * cr b * a := (mul_assoc _ _ _).symm
    _ = cr ((b ⇨ₗ c) * b) * a := by rw [cr_compositionality]
    _ ≤ cr c * a := mul_le_mul_left
        (cr_monotonicity (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl)) _
    _ = c := hc.symm

/-- Uniqueness: `x = ⌃x * a` has at most one solution — so `aᴴ` is not just
the *least* solution, it is the *only* solution. -/
theorem howe_unique {a b c : α} (hb : b = cr b * a) (hc : c = cr c * a) : b = c :=
  le_antisymm (howe_solution_le hb hc) (howe_solution_le hc hb)

/-- Usable form of uniqueness: anything satisfying the Howe equation *is* the
Howe extension. Lets an alternative construction be identified with `howe`. -/
theorem howe_eq_of_fixpoint {a b : α} (hb : b = cr b * a) : b = howe a :=
  howe_unique hb (howe_fixpoint a)



/-! ### Laws of `·ᴴ`

Monotonicity comes from the fixed-point interface alone; the identity law
needs uniqueness, since it is proved by exhibiting `Δ` as a solution and
appealing to `howe_eq_of_fixpoint`. -/

/-- `·ᴴ` is monotone. -/
theorem howe_monotonicity ⦃a b : α⦄ (h : a ≤ b) : howe a ≤ howe b := by
  refine howe_induction ?_
  calc cr (howe b) * a
      ≤ cr (howe b) * b := mul_le_mul_right h _
    _ = howe b := (howe_fixpoint b).symm
/-- The Howe extension fixes the identity: `Δᴴ = Δ`. Derived, not assumed:
`Δ = ⌃Δ * Δ` by `cr_one` and `mul_one`, so `howe_eq_of_fixpoint` identifies `Δ`
with `howe Δ`. -/
theorem howe_one : howe (1 : α) = 1 := (howe_eq_of_fixpoint (by rw [cr_one, mul_one])).symm




/-! ### The op-Howe mirror `·§`

Taking `·ᵒ` of `howe_fixpoint` gives `(aᴴ)ᵒ = aᵒ * ⌃((aᴴ)ᵒ)`: the *dual*
equation `x = a * ⌃x`, with the composition on the other side. So the
converse of a Howe extension solves the dual equation, not the original one,
and that dual has to be built separately: same recursor-plus-Knaster–Tarski
scheme, same uniqueness argument, with the right residual `⇨ᵣ` in place of
the left one. `howe_converse` closes the circle: `(aᴴ)ᵒ = (aᵒ)§`. -/

/-- Op-Howe recursor `x ↦ a * ⌃x`, bundled as an `OrderHom` so its least
fixed point can be taken via `OrderHom.lfp`. Mirror of `howeRecursor`, with
`a` on the left of `⌃x` instead of the right. -/
def opHoweRecursor (a : α) : α →o α where
  toFun x := a * cr x
  monotone' _ _ h := mul_le_mul_right (cr_monotonicity h) a

/-- Op-Howe extension `·§`: the unique solution of `x = a * ⌃x`, obtained
as the least fixed point of `opHoweRecursor`. Mirror of `howe`. -/
def opHowe (a : α) : α := (opHoweRecursor a).lfp

/-- Fixed-point law: `a§ = a * ⌃(a§)`. -/
theorem opHowe_fixpoint (a : α) : opHowe a = a * cr (opHowe a) :=
  ((opHoweRecursor a).map_lfp).symm

/-- Fixed-point induction: `a§` is below every pre-fixed point of the
op-Howe recursor. -/
theorem opHowe_induction ⦃a x : α⦄ (h : a * cr x ≤ x) : opHowe a ≤ x :=
  (opHoweRecursor a).lfp_le h

/-- Any two solutions of `x = a * ⌃x` bound each other. -/
private theorem opHowe_solution_le {a b c : α} (hb : b = a * cr b) (hc : c = a * cr c) : b ≤ c := by
  rw [show b = b * 1 from (mul_one b).symm]
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine one_le_of_cr_le ?_
  refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
  calc b * cr (b ⇨ᵣ c)
      = (a * cr b) * cr (b ⇨ᵣ c) := by rw [← hb]
    _ = a * (cr b * cr (b ⇨ᵣ c)) := mul_assoc _ _ _
    _ = a * cr (b * (b ⇨ᵣ c)) := by rw [cr_compositionality]
    _ ≤ a * cr c := mul_le_mul_right
        (cr_monotonicity (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl)) _
    _ = c := hc.symm

/-- Uniqueness: `x = a * ⌃x` has at most one solution, so `a§` is not just
the *least* solution, it is the *only* solution. -/
theorem opHowe_unique {a b c : α} (hb : b = a * cr b) (hc : c = a * cr c) : b = c :=
  le_antisymm (opHowe_solution_le hb hc) (opHowe_solution_le hc hb)

/-- Anything satisfying the op-Howe equation equals `opHowe`. -/
theorem opHowe_eq_of_fixpoint {a b : α} (hb : b = a * cr b) : b = opHowe a :=
  opHowe_unique hb (opHowe_fixpoint a)

/-- Converse of Howe is op-Howe of converse: `(aᴴ)ᵒ = (aᵒ)§`. -/
theorem howe_converse (a : α) : (howe a)ᵒ = opHowe (aᵒ) := by
  refine opHowe_eq_of_fixpoint ?_
  calc (howe a)ᵒ
      = (cr (howe a) * a)ᵒ := by rw [← howe_fixpoint]
    _ = aᵒ * (cr (howe a))ᵒ := IsInvolutiveQuantale.converse_compositionality _ _
    _ = aᵒ * cr ((howe a)ᵒ) := by rw [cr_converse_commutation]



/-! ### Closedness: residual of substitution -/

/-- Right adjoint of `·⟦b⟧`: the largest `a` such that `a⟦b⟧ ≤ c`. -/
def substResid (b c : α) : α := sSup {a | SRA.subst a b ≤ c}

/-- The substitution/residual adjunction `·⟦b⟧ ⊣ b » ·`. -/
theorem subst_le_iff {a b c : α} : SRA.subst a b ≤ c ↔ a ≤ substResid b c := by
  refine ⟨fun h => le_sSup h, fun h => ?_⟩
  calc SRA.subst a b
      ≤ SRA.subst (substResid b c) b := subst_monotonicity_left h
    _ = sSup ((fun x => SRA.subst x b) '' {x | SRA.subst x b ≤ c}) :=
        SRA.subst_join_preservation_left _ _
    _ ≤ c := by
        refine sSup_le ?_
        rintro _ ⟨y, hy, rfl⟩
        exact hy

/-- `Δ⟦Δ⟧ = Δ`: substituting the identity into the identity is the identity. -/
theorem subst_one_one : SRA.subst (1 : α) 1 = 1 := by
  refine le_antisymm ?_ ?_
  · refine subst_le_iff.mpr ?_
    refine one_le_of_cr_le ?_
    refine sup_le ?_ ?_
    · exact subst_le_iff.mp (by rw [SRA.subst_varDiag_unit_left])
    · refine subst_le_iff.mp ?_
      calc SRA.subst (scr (substResid (1 : α) 1)) 1
          ≤ scr (SRA.subst (substResid (1 : α) 1) 1) := SRA.subst_scr_oplaxity _ _
        _ ≤ scr 1 := SRA.scr_monotonicity (subst_le_iff.mpr le_rfl)
        _ ≤ 1 := scr_unit_oplaxity
  · calc (1 : α)
        = SRA.subst varDiag 1 := (SRA.subst_varDiag_unit_left 1).symm
      _ ≤ SRA.subst 1 1 := subst_monotonicity_left varDiag_coreflexivity

/-- The base instance is idempotent: `(a⟦Δ⟧)⟦Δ⟧ = a⟦Δ⟧`. -/
theorem subst_one_idempotence (a : α) :
    SRA.subst (SRA.subst a 1) 1 = SRA.subst a 1 := by
  rw [SRA.subst_associativity, subst_one_one]

/-- Compatibility implies Leibniz: if `⌃a ≤ a` then `Δ⟦a⟧ ≤ a`. -/
theorem subst_one_le_of_cr_le {a : α} (h : SRA.cr a ≤ a) :
    SRA.subst 1 a ≤ a := by
  refine subst_le_iff.mpr ?_
  refine one_le_of_cr_le ?_
  refine subst_le_iff.mp ?_
  calc SRA.subst (SRA.cr (SRA.substResid a a)) a
      ≤ a ⊔ SRA.cr (SRA.subst (SRA.substResid a a) a) := subst_cr_oplaxity _ _
    _ ≤ a ⊔ SRA.cr a := sup_le_sup_left (cr_monotonicity (subst_le_iff.mpr le_rfl)) a
    _ ≤ a ⊔ a := sup_le_sup_left h a
    _ = a := sup_idem a



/-! ### Notation -/

@[inherit_doc] scoped postfix:max "ᴴ" => SRA.howe
@[inherit_doc] scoped postfix:max "§" => SRA.opHowe

end SRA
