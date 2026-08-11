/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.OperationalDecomposition

/-!
# Canonical terms

Definition A.3 and Lemma A.4 of the draft: the predicates
`RespectsCanonicalTerms` and `RespectsCompleteTerms`, and the five
laws (RC1)–(RC5) that hold of every reduction under the standing
assumptions (GIP and Inv). Lemma A.5, law (C19).

**Status.** The proofs of (RC1)–(RC5) and (C19) are **not** given in the
draft; they are stated as facts that follow from the standing assumptions
(GIP and Inv). Proofs are left as `sorry` pending derivation from those
assumptions.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Definition A.3, Lemma A.4, Lemma A.5.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- A relation `a` respects canonical terms when it is oplax-commutative
with the introduction diagonal on the left: `‾Δ ; a ≤ a ; ‾Δ`. -/
def RespectsCanonicalTerms (a : α) : Prop := introDiag * a ≤ a * introDiag

/-- A relation `a` respects complete terms when it is oplax-commutative
with the value diagonal on the left: `Δκ ; a ≤ a ; Δκ`. -/
def RespectsCompleteTerms (a : α) : Prop := SRA.box 1 * a ≤ a * SRA.box 1

/-- Law (RC1): `‾Δ * SRA.cr a ≤ SRA.cr a * ‾Δ`. -/
theorem RC1 (a : α) : introDiag * SRA.cr a ≤ SRA.cr a * introDiag := by
  sorry

/-- Law (RC2): `Δκ * SRA.box (SRA.cr a) ≤ SRA.box (SRA.cr a) * Δκ`. -/
theorem RC2 (a : α) : valDiag * SRA.box (SRA.cr a) ≤ SRA.box (SRA.cr a) * valDiag := by
  sorry

/-- Law (RC3): `Δκ * elim a b ≤ elim a b * Δκ`. -/
theorem RC3 (a b : α) : SRA.box 1 * elim a b ≤ elim a b * SRA.box 1 := by
  sorry

/-- Law (RC4): `Δκ * elim a b ≤ SRA.box (elim a b)`. -/
theorem RC4 (a b : α) : SRA.box 1 * elim a b ≤ SRA.box (elim a b) := by
  sorry

/-- Law (RC5): `Δκ * elim a b ≤ SRA.box (c * elim a b)`. -/
theorem RC5 (a b c : α) : SRA.box 1 * elim a b ≤ SRA.box (c * elim a b) := by
  sorry

/-- Law (C19): `SRA.cr a * elim b c ≤ elim a a * elim b c`. -/
theorem C19 (a b c : α) : SRA.cr a * elim b c ≤ elim a a * elim b c := by
  sorry

#print axioms OperationalDecomposition.RespectsCanonicalTerms
#print axioms OperationalDecomposition.RespectsCompleteTerms
#print axioms OperationalDecomposition.RC1
#print axioms OperationalDecomposition.RC2
#print axioms OperationalDecomposition.RC3
#print axioms OperationalDecomposition.RC4
#print axioms OperationalDecomposition.RC5
#print axioms OperationalDecomposition.C19

end OperationalDecomposition
