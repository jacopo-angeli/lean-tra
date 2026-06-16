import Allegory.TRA.Reduction.Parallel

/-!
# R4 — Orthogonality Condition

Defines the orthogonality predicate consumed by the algebraic confluence theorem
(Gavazzo, LICS 2026, Theorem 21 antecedent). A reduction `a` is orthogonal when
its substitution instances are deterministic (`a[Δ]° ; a[Δ] ≤ Δ`) and parallel
sub-reduction preserves redex structure (`a[Δ]° ; ã[Δ]⇛ ≤ a° [a⇛]`). Lemma 36 in
`Allegory/TRA/Bridge/Lemma36.lean` derives this condition from GIP + GCP, and
Theorem 21 in `Allegory/TRA/Reduction.lean` consumes it to obtain confluence.

## Main definitions

* `Allegory.TRA.DeterministicSubstInstances` — `a[Δ]° ; a[Δ] ≤ Δ`
* `Allegory.TRA.ParallelRedexPreserved` — `a[Δ]° ; ã[Δ]⇛ ≤ a° [a⇛]`
* `Allegory.TRA.Orthogonal` — conjunction of the two clauses above

## Main results

* `Allegory.TRA.deterministic_left_cancellation` — left-cancellation form `a[Δ]° ; a[Δ] ; R ≤ R`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Theorem 21
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A]

/-- **Deterministic substitution instances** (Paper 2026, Thm. 21
antecedent, first clause): `a[Δ]° ; a[Δ] ≤ Δ`. -/
def DeterministicSubstInstances {X : A} (a : X ⟶ X) : Prop :=
  converse (substitution a (𝟙 X)) ≫ substitution a (𝟙 X) ≤ 𝟙 X

/-- **Parallel-reduction redex preservation** (Paper 2026, Thm. 21
antecedent, second clause): `a[Δ]° ; ã[Δ]⇛ ≤ a° [a⇛]`. Here
`ã := delta_eta ⊔ tilde a` is the derived strict compatible refinement
(paper's `˜·`, file's `hat`). -/
def ParallelRedexPreserved {X : A} (a : X ⟶ X) : Prop :=
  converse (substitution a (𝟙 X))
    ≫ parallelReduction (substitution (delta_eta ⊔ tilde a) (𝟙 X))
    ≤ substitution (converse a) (parallelReduction a)

/-- **R4 — Orthogonal** (Paper 2026, Thm. 21 antecedent): a relation
`a` is orthogonal when both substitution instances are deterministic and
parallel sub-reduction preserves redex structure. -/
def Orthogonal {X : A} (a : X ⟶ X) : Prop :=
  DeterministicSubstInstances a ∧ ParallelRedexPreserved a

/-- **Deterministic ⟹ left-cancellation**: from `a[Δ]° ; a[Δ] ≤ Δ` we
obtain `a[Δ]° ; a[Δ] ; R ≤ R` for any `R`, the form needed downstream
(Lemma 36 / R5). -/
theorem deterministic_left_cancellation {X : A} (a : X ⟶ X)
    (_h : DeterministicSubstInstances a) (R : X ⟶ X) :
    converse (substitution a (𝟙 X)) ≫ substitution a (𝟙 X) ≫ R ≤ R := by
  -- deps: Category.assoc, Category.id_comp, LocallyCompleteAllegory.iSup_comp_left
  sorry

end Allegory.TRA
