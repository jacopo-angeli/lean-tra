import Allegory.TRA.Similarity.Basic

/-!
# S2 — op-Howe Extension `a§`

The op-Howe extension `a§ := (♢a)ᴴ°` is the converse of the Howe extension of
the open extension of `a` (Gavazzo, LICS 2026, §6.1.1). For any closed preorder
`a` it satisfies the four §-properties — reflexivity `Δ ≤ a§`, substitutivity
`a§[a§] ≤ a§`, compatibility `â§ ≤ a§`, and quasi-transitivity
`♢a ; a§ ≤ a§` — which together drive the congruence proof of Theorem 35 (S4) in
`Allegory/TRA/Similarity/Theorem35.lean` via Lemma 34 (S3).

## Main definitions

* `Allegory.TRA.opHowe` — `a§ := (♢a)ᴴ°`

## Main results

* `Allegory.TRA.opHowe_reflexive` — §1: closed preorder ⟹ `𝟙 ≤ a§`
* `Allegory.TRA.opHowe_substitutive` — §2: `a§[a§] ≤ a§`
* `Allegory.TRA.opHowe_compatible` — §3: `tilde (a§) ≤ a§`
* `Allegory.TRA.opHowe_quasi_transitive` — §4: `♢a ; a§ ≤ a§`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, §6.1.1
* Howe, D., *Proving congruence of bisimulation in functional programming languages*, 1996
* Lassen, S., *Relational reasoning about functions and nondeterminism*, 1998
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **S2 — op-Howe extension** `a§ := (♢a)ᴴ°` (Paper 2026, Sec. 6.1.1):
converse of the Howe extension of the open extension of `a`. -/
def opHowe {X : A} (a : X ⟶ X) : X ⟶ X :=
  converse (howe (openExt a))

/-- **§1 — Reflexivity** (Paper 2026, Sec. 6.1.1: "Δ ≤ a§"): closed
preorder ⟹ `a§` is reflexive. -/
theorem opHowe_reflexive {X : A} (a : X ⟶ X)
    (_hClosed : Closed a) (_hRefl : 𝟙 X ≤ a) (_hTrans : a ≫ a ≤ a) :
    𝟙 X ≤ opHowe a := by
  -- deps: Allegory.converse_id, compatible_reflexive, howe_fixed_point
  sorry

/-- **§2 — Substitutivity** (Paper 2026, Sec. 6.1.1: "a§[a§] ≤ a§"):
the op-Howe extension is substitutive. -/
theorem opHowe_substitutive {X : A} (a : X ⟶ X)
    (_hClosed : Closed a) (_hRefl : 𝟙 X ≤ a) (_hTrans : a ≫ a ≤ a) :
    substitution (opHowe a) (opHowe a) ≤ opHowe a := by
  -- deps: substitution_converse_left, substitution_converse_right, howe_fixed_point, Substitutive
  sorry

/-- **§3 — Compatibility** (Paper 2026, Sec. 6.1.1: "â§ ≤ a§"):
the op-Howe extension is compatible. -/
theorem opHowe_compatible {X : A} (a : X ⟶ X) :
    tilde (opHowe a) ≤ opHowe a := by
  -- deps: tilde_converse, howe_fixed_point, Compatible
  sorry

/-- **§4 — Quasi-transitivity** (Paper 2026, Sec. 6.1.1:
"♢a ; a§ ≤ a§"): the open extension left-absorbs into `a§`. -/
theorem opHowe_quasi_transitive {X : A} (a : X ⟶ X)
    (_hClosed : Closed a) (_hRefl : 𝟙 X ≤ a) (_hTrans : a ≫ a ≤ a) :
    openExt a ≫ opHowe a ≤ opHowe a := by
  -- deps: Allegory.converse_composition, Allegory.converse_involution, howe_fixed_point, openExt, box_le_self
  sorry

end Allegory.TRA
