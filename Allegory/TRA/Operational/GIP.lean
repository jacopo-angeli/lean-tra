import Allegory.TRA.Operational.Decomposition

/-!
# O2 — Gentzen's Inversion Principle (GIP)

Gentzen's Inversion Principle (Gavazzo, LICS 2026, Definition 24) characterises
computations as the interaction between elimination forms and introduction
forms. A relation `a` satisfies GIP when `a ≤ ⟨Δ⟩ ; a`, i.e. every computation
can be factored through an elimination context whose major argument is already
an introduction form. This expresses a structural stability principle:
computation does not introduce new computational content beyond what is already
present in the syntactic constructors. In equational form GIP yields
`a = ⟨Δ⟩ ; a`, and a key consequence is that GIP forces orthogonality of
variable reduction — no interaction between variable coreflexives and
computational content is possible. GIP is consumed by Lemma 36 (M1) and by the
determinism proof for big-step evaluation (B4).

## Main definitions

* `Allegory.TRA.GIP` — Gentzen's Inversion Principle on a relation `a`

## Main results

* `Allegory.TRA.gip_eq` — equational form `a = ⟨Δ⟩ ; a` under GIP
* `Allegory.TRA.gip_delta_eta_orthogonal` — GIP excludes variable reductions: `Δη ; a ≤ ⊥`

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026, Definition 24
-/

open CategoryTheory

namespace Allegory.TRA

variable {A : Type*} [TRA A] [OperationalDecomposition A]

/-- **O2 — GIP** (Paper 2026, Def. 24): `a` satisfies Gentzen's Inversion
Principle iff `a ≤ ⟨Δ⟩ ; a`, where `⟨Δ⟩ ≜ ⟨Δ, Δ⟩` is the destructor
bracket of identities (`bracketSingle (𝟙 X)`). -/
def GIP {X : A} (a : X ⟶ X) : Prop := a ≤ bracketSingle (𝟙 X) ≫ a

/-- **GIP equational form** (Paper 2026, Def. 24: "i.e. a = ⟨Δ⟩;a"):
under GIP the inequality is an equality, since `⟨Δ⟩ ≤ Δ` from the
cocartesian decomposition. -/
theorem gip_eq {X : A} (a : X ⟶ X) (_h : GIP a) :
    a = bracketSingle (𝟙 X) ≫ a := by
  -- deps: tilde_decomposition, howe_delta, howe_fixed_point, Category.id_comp, le_antisymm
  sorry

/-- **GIP excludes variable reductions** (Paper 2026, p. 76:19,
"Implies ∆η;a=⊥ for reductions"): if `a` satisfies GIP, no variable is
reducible. -/
theorem gip_delta_eta_orthogonal {X : A} (a : X ⟶ X) (_h : GIP a) :
    delta_eta ≫ a ≤ ⊥ := by
  -- deps: cocartesian_orthogonality, tilde_decomposition, LocallyCompleteAllegory.iSup_comp_left
  sorry

end Allegory.TRA
