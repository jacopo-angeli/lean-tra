import Allegory.TRA.Operational.GIP
import Allegory.TRA.Operational.GCP
import Allegory.TRA.Reduction.Parallel
import Allegory.TRA.Reduction.Orthogonality

/-!
# M1 — Lemma 36: GCP + GIP imply Orthogonality

Lemma 36 (Gavazzo, LICS 2026, §6): a reduction satisfying GCP and GIP yields the
orthogonality condition required by Theorem 21 (R5):
`a[Δ]° ; ã[Δ]⇛ ≤ a°[a⇛]`. The argument is a short equational manipulation built
around the key inequality `x ; a⇛ ≤ x̂ ; a⇛`. This file is the operational
bridge feeding clause (i) of the Bridge Theorem (M2) in
`Allegory/TRA/Bridge.lean`.

## Main results

* `Allegory.TRA.parallelReduction_compatible_absorb` — key inequality `x ; a⇛ ≤ x̂ ; a⇛`
* `Allegory.TRA.gip_gcp_imp_orthogonality` — Lemma 36: GIP + GCP imply orthogonality
* `Allegory.TRA.orthogonal_of_gip_gcp` — corollary restated against R4's `Orthogonal` predicate

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Lemma 36
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **Compatible left-absorption** (Paper 2026, Lemma 36 proof, key
inequality: for any relation `x`,
`x ; a⇛ ≤ x̂ ; a⇛`. -/
theorem parallelReduction_compatible_absorb {X : A} (a x : X ⟶ X) :
    x ≫ parallelReduction a ≤ tilde x ≫ parallelReduction a := by
  -- deps: parallelReduction, parallelReduction_fixed_point, howe_fixed_point, tilde, LocallyCompleteAllegory.comp_iSup_right
  sorry

/-- **Lemma 36** (Paper 2026, p. 76:25) — **bridge to orthogonality**:
a reduction satisfying GIP and GCP satisfies the orthogonality
condition `a[Δ]° ; ã[Δ]⇛ ≤ a°[a⇛]`. -/
theorem gip_gcp_imp_orthogonality {X : A} (a : X ⟶ X)
    (_hRed : Reduction a) (_hGIP : GIP a) (_hGCP : GCP a) :
    converse (substitution a delta_eta)
        ≫ parallelReduction (substitution (tilde a) delta_eta)
      ≤ substitution (converse a) (parallelReduction a) := by
  -- deps: parallelReduction_compatible_absorb, parallelReduction, parallelReduction_fixed_point, GIP, gip_eq, GCP, Reduction, substitution_converse_left, substitution_converse_right, substitution_monotonicity_left, substitution_monotonicity_right
  sorry

/-- **Corollary — Orthogonal reduction from GIP + GCP** (Paper 2026,
Lemma 36, restated against R4's `Orthogonal` predicate): under the
hypotheses, `a` qualifies as orthogonal so Theorem 21 (R5) applies. -/
theorem orthogonal_of_gip_gcp {X : A} (a : X ⟶ X)
    (_hRed : Reduction a) (_hGIP : GIP a) (_hGCP : GCP a)
    (_hDet : DeterministicSubstInstances a) : Orthogonal a := by
  -- deps: gip_gcp_imp_orthogonality, Orthogonal, DeterministicSubstInstances, ParallelRedexPreserved
  sorry

end Allegory.TRA
