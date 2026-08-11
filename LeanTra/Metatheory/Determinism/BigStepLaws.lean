/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Evaluation
public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Metatheory.CanonicalTerms

/-!
# Big-step evaluation laws

Lemma A.6 and Figures 7–8 of the draft: the basic laws of big-step
evaluation for closed reductions.  (F4) is `bigStep_le_of_closed` above;
(F6), (F10), and (F11) consume `valDiag_mul_self` from Part B and
therefore inherit its `sorry`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Lemma A.6, Figures 7 and 8.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- Lemma A.6, first half: for a closed reduction,
`a⇓ = Δκ ⊔ a * a⇓ ⊔ maj a⇓ * a⇓`. -/
theorem bigStep_fix_closed {a : α} (h : a = SRA.box a) :
    bigStep a = valDiag ⊔ a * bigStep a ⊔ maj (bigStep a) * bigStep a := by
  sorry

/-- Lemma A.6, second half: for a closed reduction, if
`Δκ ⊔ a * x ⊔ maj x * x ≤ x` then `a⇓ ≤ x`. -/
theorem bigStep_le_of_closed {a x : α} (h : a = SRA.box a)
    (hx : valDiag ⊔ a * x ⊔ maj x * x ≤ x) : bigStep a ≤ x := by
  sorry

/-! ### Figure 7 — basic laws of big-step evaluation -/

/-- Law (F1): `valDiag ≤ bigStep a`. -/
theorem F1 (a : α) : (valDiag : α) ≤ bigStep a := by
  sorry

/-- Law (F2): `a * bigStep a ≤ bigStep a`. -/
theorem F2 (a : α) : a * bigStep a ≤ bigStep a := by
  sorry

/-- Law (F3): `maj (bigStep a) * bigStep a ≤ bigStep a`. -/
theorem F3 (a : α) : maj (bigStep a) * bigStep a ≤ bigStep a := by
  sorry

/-- Law (F4): `bigStep a ≤ x` whenever
`valDiag ⊔ a * x ⊔ maj x * x ≤ x`, for closed `a`. -/
theorem F4 (a x : α) (hclosed : a = SRA.box a)
    (hx : valDiag ⊔ a * x ⊔ maj x * x ≤ x) : bigStep a ≤ x :=
  bigStep_le_of_closed hclosed hx

/-- Law (F5): `bigStep 1 ≤ 1`. -/
theorem F5 : bigStep (1 : α) ≤ 1 := by
  sorry

/-- Law (F6): `bigStep a = bigStep a * valDiag`.

**Status.** Both directions consume `valDiag_mul_self` from Part B and
therefore inherit its `sorry`. -/
theorem F6 (a : α) : bigStep a = bigStep a * (valDiag : α) := by
  sorry

/-- Law (F7): `a ≤ b → bigStep a ≤ bigStep b`. -/
theorem F7 {a b : α} (h : a ≤ b) : bigStep a ≤ bigStep b := by
  sorry

/-- Law (F8): `a ≤ SRA.box a → bigStep a ≤ SRA.box (bigStep a)`. -/
theorem F8 {a : α} (h : a ≤ SRA.box a) : bigStep a ≤ SRA.box (bigStep a) := by
  sorry

/-- Law (F9): if `valDiag ⊔ b * aᵒ ⊔ b * maj b ≤ b` then `(bigStep a)ᵒ ≤ b`. -/
theorem F9 {a b : α}
    (h : (valDiag : α) ⊔ b * aᵒ ⊔ b * maj b ≤ b) : (bigStep a)ᵒ ≤ b := by
  sorry

/-- Law (F10): `valDiag * bigStep a = valDiag` when `a` is invertible.

**Status.** Consumes `valDiag_mul_self` from Part B and therefore inherits
its `sorry`. -/
theorem F10 (a : α) (hinv : Inv a) : (valDiag : α) * bigStep a = valDiag := by
  sorry

/-- Law (F11): `bigStep a * (bigStep a)ᵒ = bigStep a` when `a` is invertible.

**Status.** Consumes `valDiag_mul_self` from Part B and therefore inherits
its `sorry`. -/
theorem F11 (a : α) (hinv : Inv a) : bigStep a * (bigStep a)ᵒ = bigStep a := by
  sorry

#print axioms OperationalDecomposition.bigStep_fix_closed
#print axioms OperationalDecomposition.bigStep_le_of_closed
#print axioms OperationalDecomposition.F1
#print axioms OperationalDecomposition.F2
#print axioms OperationalDecomposition.F3
#print axioms OperationalDecomposition.F4
#print axioms OperationalDecomposition.F5
#print axioms OperationalDecomposition.F6
#print axioms OperationalDecomposition.F7
#print axioms OperationalDecomposition.F8
#print axioms OperationalDecomposition.F9
#print axioms OperationalDecomposition.F10
#print axioms OperationalDecomposition.F11

end OperationalDecomposition
