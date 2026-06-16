import Allegory.TRA.Operational.Decomposition
import Allegory.TRA.Properties

/-!
# O3 — Gentzen's Conservation Principle (GCP)

Gentzen's Conservation Principle (Gavazzo, LICS 2026, Definition 33) expresses
that computation is stable under parametric substitution of compatible
contexts. A relation `a` satisfies GCP when for every compatible `x`,
`⟨x̂, x⟩ ; a ≤ a ; x[x]`. This states that applying a computation after
introducing a structured context is always bounded by first substituting inside
the context and then computing: computation commutes with compatible structure
and no new behaviour is created by wrapping a term in a compatible
elimination–introduction pair. GCP is the parametricity principle consumed by
Lemma 36 (M1) in `Allegory/TRA/Bridge/Lemma36.lean` and by Theorem 35 (S4) in
`Allegory/TRA/Similarity/Theorem35.lean`.

## Main definitions

* `Allegory.TRA.GCP` — Gentzen's Conservation Principle on a relation `a`

## Main results

* `Allegory.TRA.gcp_at_delta` — corollary of GCP at `x := Δ`: `⟨Δ⟩ ; a ≤ a ; Δ[Δ]`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 33
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **O3 — GCP** (Paper 2026, Def. 33): `a` satisfies Gentzen's
Conservation Principle iff for every *compatible* `x : X ⟶ X`,
`⟨x̂, x⟩ ; a ≤ a ; x[x]`, where `x̂` is the file's `tilde x` (paper's
Howe-extension component `ˆ·`). -/
def GCP {X : A} (a : X ⟶ X) : Prop := ∀ (x : X ⟶ X), Compatible x → OperationalDecomposition.bracketRel (tilde x) x ≫ a ≤ a ≫ substitution x x

/-- **GCP instantiated at `Δ`** (corollary, used in Lemma 36): since `Δ`
is compatible (because `tilde Δ = Δ`, derived from Condition 2), GCP at
`x := Δ` reduces to `⟨Δ⟩ ; a ≤ a ; Δ[Δ]`. -/
theorem gcp_at_delta {X : A} (a : X ⟶ X) (_h : GCP a) :
    bracketSingle (𝟙 X) ≫ a ≤ a ≫ substitution (𝟙 X) (𝟙 X) := by
  -- deps: howe_delta, howe_fixed_point, Category.comp_id, bracketSingle, Compatible
  sorry

end Allegory.TRA
