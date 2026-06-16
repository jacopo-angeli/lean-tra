import Allegory.TRA.Reduction.Confluence
import Allegory.TRA.Reduction.Orthogonality

/-!
# R5 — Theorem 21: Confluence of Orthogonal Reduction

Algebraic confluence theorem for TRAs (Gavazzo, LICS 2026, Theorem 21): if `a`
is orthogonal then parallel reduction `a⇛` has the diamond property, and hence
`a⇛` is confluent. Conjoining this with Lemma 36 (M1) gives clause (i) of the
Bridge Theorem (M2) in `Allegory/TRA/Bridge.lean`.

## Main results

* `Allegory.TRA.orthogonal_imp_parallelReduction_diamond` — orthogonal ⟹ `a⇛` has the diamond property
* `Allegory.TRA.orthogonal_imp_parallelReduction_confluent` — orthogonal ⟹ `a⇛` is confluent

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Theorem 21
-/

open CategoryTheory Allegory

namespace Allegory.TRA

variable {A : Type*} [TRA A]

/-- **Theorem 21** (Paper 2026, p. 76:18): if `a` is orthogonal, then
parallel reduction `a⇛` has the diamond property. -/
theorem orthogonal_imp_parallelReduction_diamond {X : A} (a : X ⟶ X)
    (_h : Orthogonal a) :
    Diamond (parallelReduction a) := by
  -- deps: parallelReduction_fixed_point, tilde_converse, tilde_composition, howe_uniqueness, converse_composition, converse_involution, Orthogonal.1, Orthogonal.2
  sorry

/-- **Corollary of Theorem 21** (Paper 2026, p. 76:18): orthogonal `a`
implies parallel reduction `a⇛` is confluent. -/
theorem orthogonal_imp_parallelReduction_confluent {X : A} (a : X ⟶ X)
    (h : Orthogonal a) :
    Confluent (parallelReduction a) := by
  -- deps: orthogonal_imp_parallelReduction_diamond, Allegory.confluent_of_diamond
  sorry

end Allegory.TRA
