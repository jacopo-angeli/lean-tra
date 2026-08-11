/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.GentzenPrinciples
public import LeanTra.Algebra.KleeneStar

/-!
# Operational semantics: evaluation recursor and big-step evaluation

The evaluation recursor `evalRec` (written `aᶠ`), one-step evaluation
`oneStep` (written `aᴱ`), and big-step evaluation `bigStep` (written `a⇓`),
along with their characterising fixed-point laws and induction principles.

## Notation warning

In the accompanying PDF the introduction operation carries an OVERLINE
that is invisible to text extraction. Every occurrence of `Δ` inside
the operational-semantics chapter is `‾Δ = introduction 1`, NOT the base
identity `Δη = 1`. Here `introductionCoreflexive` denotes `‾Δ`; the plain
`(1 : α)` is unchanged.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, one-step and big-step evaluation, and the transfer of the
  closure modality to big-step evaluation.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale LeanTra.Confluence

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- Notice that the orthogonality gives `introduction a * elimination b c ≤ ⊥`,
meaning that constructors and destructors are disjoint. -/
theorem elimination_introduction_orthogonality (a b c : α) :
    OperationalDecomposition.elimination a b
      * OperationalDecomposition.introduction c ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_le_converse_iff,
      IsInvolutiveQuantale.converse_bot,
      IsInvolutiveQuantale.mul_converse,
      ← OperationalDecomposition.introduction_morphism_converse,
      ← OperationalDecomposition.elimination_morphism_converse]
  exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _

/-- The major-slot projection composed with the value-diagonal on the
right lands in `⊥`. -/
theorem maj_mul_introDiag_le_bot (a : α) :
    majorProjection a * (introductionCoreflexive : α) ≤ ⊥ := by
  change OperationalDecomposition.elimination a 1
     * OperationalDecomposition.introduction 1 ≤ ⊥
  exact elimination_introduction_orthogonality _ _ _

/-- The introduction-coreflexive is idempotent under multiplication:
`introductionCoreflexive * introductionCoreflexive = introductionCoreflexive`. -/
theorem introDiag_mul_self :
    (introductionCoreflexive : α) * introductionCoreflexive = introductionCoreflexive := by
  change OperationalDecomposition.introduction 1
       * OperationalDecomposition.introduction 1
     = OperationalDecomposition.introduction 1
  rw [← OperationalDecomposition.introduction_morphism_composition, one_mul]

/-- The evaluation-recursor step `x ↦ (‾Δ ⊔ ⟨x⟩) * a`, bundled as an
`OrderHom` for `OrderHom.lfp`. -/
def evalStep (a : α) : α →o α where
  toFun x := ((introductionCoreflexive : α) ⊔ majorProjection x) * a
  monotone' _ _ h := by
    exact mul_le_mul' (sup_le_sup_left
      (elimination_monotonicity h le_rfl) _) le_rfl

/-- The evaluation recursor `aᶠ`: the least fixed point of `evalStep a`. -/
def evalRec (a : α) : α := (evalStep a).lfp

/-- Fixed-point law for `evalRec`. -/
theorem evalRec_fix (a : α) :
    evalRec a = ((introductionCoreflexive : α) ⊔ majorProjection (evalRec a)) * a := by
  change (evalStep a).lfp
        = ((introductionCoreflexive : α) ⊔ majorProjection (evalStep a).lfp) * a
  exact ((evalStep a).map_lfp).symm

/-- Least-prefix-point induction for `evalRec`. -/
theorem evalRec_le_of {a x : α}
    (h : ((introductionCoreflexive : α) ⊔ majorProjection x) * a ≤ x) :
    evalRec a ≤ x :=
  (evalStep a).lfp_le h

/-- One-step evaluation `aᴱ := (a ⊔ ‾Δ)ᶠ`. -/
def oneStep (a : α) : α := evalRec (a ⊔ introductionCoreflexive)

/-- Big-step evaluation `a⇓ := (aᴱ)∗ * ‾Δ`. -/
def bigStep (a : α) : α := (oneStep a)∗ * introductionCoreflexive

private theorem evalStep_apply_a_sup_introductionCoreflexive
    {a : α} (hGIP : GIP a) (x : α) :
    ((introductionCoreflexive : α) ⊔ majorProjection x) * (a ⊔ introductionCoreflexive)
      = introductionCoreflexive ⊔ majorProjection x * a := by
  rw [Quantale.mul_sup_distrib, Quantale.sup_mul_distrib,
      Quantale.sup_mul_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact (introduction_mul_of_gip hGIP _).trans bot_le
    · exact le_sup_right
    · exact introDiag_mul_self.le.trans le_sup_left
    · exact (maj_mul_introDiag_le_bot _).trans bot_le
  · refine sup_le ?_ ?_
    · exact le_sup_of_le_right
        (le_sup_of_le_left introDiag_mul_self.ge)
    · exact le_sup_of_le_left le_sup_right

/-- Under `GIP a`, one-step evaluation `aᴱ` satisfies its
characterising fixed-point equation. -/
theorem oneStep_fix {a : α} (hGIP : GIP a) :
    oneStep a = introductionCoreflexive ⊔ majorProjection (oneStep a) * a := by
  change evalRec (a ⊔ introductionCoreflexive)
      = introductionCoreflexive
          ⊔ majorProjection (evalRec (a ⊔ introductionCoreflexive)) * a
  conv_lhs => rw [evalRec_fix (a ⊔ introductionCoreflexive)]
  rw [evalStep_apply_a_sup_introductionCoreflexive hGIP]

/-- Under `GIP a`, one-step evaluation is the least prefix point of
`x ↦ ‾Δ ⊔ ⟨x⟩ * a`. -/
theorem oneStep_le_of {a x : α} (hGIP : GIP a)
    (h : (introductionCoreflexive : α) ⊔ majorProjection x * a ≤ x) : oneStep a ≤ x := by
  refine evalRec_le_of ?_
  rw [evalStep_apply_a_sup_introductionCoreflexive hGIP]
  exact h

private theorem introductionCoreflexive_mul_oneStep
    {a : α} (hGIP : GIP a) :
    (introductionCoreflexive : α) * oneStep a = introductionCoreflexive := by
  conv_lhs => rw [oneStep_fix hGIP]
  rw [Quantale.mul_sup_distrib, introDiag_mul_self]
  refine le_antisymm ?_ le_sup_left
  refine sup_le le_rfl ?_
  calc (introductionCoreflexive : α) * (majorProjection (oneStep a) * a)
      = introductionCoreflexive * majorProjection (oneStep a) * a := (mul_assoc _ _ _).symm
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.introduction 1
              * OperationalDecomposition.elimination (oneStep a) 1 ≤ ⊥
        exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
    _ = ⊥ := Quantale.bot_mul
    _ ≤ introductionCoreflexive := bot_le

private theorem introductionCoreflexive_mul_oneStep_star
    {a : α} (hGIP : GIP a) :
    (introductionCoreflexive : α) * (oneStep a)∗ = introductionCoreflexive := by
  refine le_antisymm ?_ ?_
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
    refine LeanTra.Confluence.star_le_of ?_
    refine sup_le ?_ ?_
    · exact Quantale.rightMulResiduation_le_iff_mul_le.mpr
        (by rw [mul_one])
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      calc (introductionCoreflexive : α)
              * (oneStep a * ((introductionCoreflexive : α) ⇨ᵣ introductionCoreflexive))
          = introductionCoreflexive * oneStep a
              * (introductionCoreflexive ⇨ᵣ introductionCoreflexive) :=
            (mul_assoc _ _ _).symm
        _ = introductionCoreflexive * (introductionCoreflexive ⇨ᵣ introductionCoreflexive) := by
            rw [introductionCoreflexive_mul_oneStep hGIP]
        _ ≤ introductionCoreflexive :=
            Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl
  · calc (introductionCoreflexive : α)
        = introductionCoreflexive * 1 := (mul_one _).symm
      _ ≤ introductionCoreflexive * (oneStep a)∗ := by
          exact mul_le_mul' le_rfl (LeanTra.Confluence.one_le_star _)

/-- Star-normal-form fixed-point law for big-step evaluation.

**Status.** This closes the star-normal form
`a⇓ = ‾Δ ∨ aᴱ ; a⇓`, which is what the modality-transfer argument
(`box_bigStep`) consumes. The paper's stated form of Prop. 29(b) is
`a⇓ = ‾Δ ∨ ⟨a⇓⟩ ; a ; a⇓`, and that form is **not proved here**.
Reducing the star-normal form to the paper's form needs the rewrite
`⟨aᴱ⟩ ⇝ ⟨a⇓⟩` inside `aᴱ ; a⇓`, which in turn needs `aᴱ ≤ a⇓`; that
inequality **fails** because `a⇓` ends with a `* ‾Δ` on the right and
`aᴱ` does not, so the two-tail-shape mismatch is not fixable without a
"right GIP" axiom (`a ≤ a * eliminationCoreflexive`) that the current
class does not carry. -/
theorem bigStep_fix (a : α) :
    bigStep a = introductionCoreflexive ⊔ oneStep a * bigStep a := by
  change (oneStep a)∗ * introductionCoreflexive
       = introductionCoreflexive
           ⊔ oneStep a * ((oneStep a)∗ * introductionCoreflexive)
  conv_lhs => rw [LeanTra.Confluence.star_fix]
  rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]

/-- Star-normal-form least-prefix-point law: `a⇓` is below every
prefix point of `x ↦ ‾Δ ⊔ aᴱ * x`. -/
theorem bigStep_le_of {a x : α}
    (h : (introductionCoreflexive : α) ⊔ oneStep a * x ≤ x) : bigStep a ≤ x := by
  have hintroductionCoreflexive : (introductionCoreflexive : α) ≤ x := le_sup_left.trans h
  have hone : oneStep a * x ≤ x := le_sup_right.trans h
  calc bigStep a
      = (oneStep a)∗ * introductionCoreflexive := rfl
    _ ≤ (oneStep a)∗ * x := by
        exact mul_le_mul' le_rfl hintroductionCoreflexive
    _ ≤ x := by
        refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
        refine LeanTra.Confluence.star_le_of ?_
        refine sup_le ?_ ?_
        · exact Quantale.leftMulResiduation_le_iff_mul_le.mpr
            (by rw [one_mul])
        · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
          calc oneStep a * (x ⇨ₗ x) * x
              = oneStep a * ((x ⇨ₗ x) * x) := mul_assoc _ _ _
            _ ≤ oneStep a * x := by
                exact mul_le_mul' le_rfl
                  (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl)
            _ ≤ x := hone

/-- Commutation of `SRA.box` with big-step evaluation, under four
explicit hypotheses.

**Status.** The hypothesis `hmul : ∀ A B, □(A * B) ≤ □A * □B` is
**refuted** in the intended first-order term model by
`LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`. This
theorem is therefore vacuous for that model and is **not** a proof of
the paper's Prop. 29(c) there. The three auxiliary "□ commutes with"
premises (`hboxIntroductionCoreflexive`, `hboxOneStep`, `hboxStar`) are
likewise not derivable from the current axioms even under `hmul`, and
are carried explicitly rather than proved. -/
theorem box_bigStep
    (hmul : ∀ A B : α, SRA.box (A * B) ≤ SRA.box A * SRA.box B)
    (a : α)
    (hboxIntroductionCoreflexive :
      SRA.box (introductionCoreflexive : α) = introductionCoreflexive)
    (hboxOneStep : SRA.box (oneStep a) = oneStep (SRA.box a))
    (hboxStar : ∀ b : α, SRA.box (b∗) = (SRA.box b)∗) :
    SRA.box (bigStep a) = bigStep (SRA.box a) := by
  refine le_antisymm ?_ ?_
  · calc SRA.box (bigStep a)
        = SRA.box ((oneStep a)∗ * introductionCoreflexive) := rfl
      _ ≤ SRA.box ((oneStep a)∗) * SRA.box introductionCoreflexive := hmul _ _
      _ = (SRA.box (oneStep a))∗ * SRA.box introductionCoreflexive := by rw [hboxStar]
      _ = (oneStep (SRA.box a))∗ * SRA.box introductionCoreflexive := by rw [hboxOneStep]
      _ = (oneStep (SRA.box a))∗ * introductionCoreflexive := by
          rw [hboxIntroductionCoreflexive]
      _ = bigStep (SRA.box a) := rfl
  · calc bigStep (SRA.box a)
        = (oneStep (SRA.box a))∗ * introductionCoreflexive := rfl
      _ = (oneStep (SRA.box a))∗ * SRA.box introductionCoreflexive := by
          rw [hboxIntroductionCoreflexive]
      _ = (SRA.box (oneStep a))∗ * SRA.box introductionCoreflexive := by rw [hboxOneStep]
      _ = SRA.box ((oneStep a)∗) * SRA.box introductionCoreflexive := by rw [hboxStar]
      _ ≤ SRA.box ((oneStep a)∗ * introductionCoreflexive) := SRA.box_mul_box_le _ _
      _ = SRA.box (bigStep a) := rfl

end OperationalDecomposition

#print axioms OperationalDecomposition.bigStep_fix
#print axioms OperationalDecomposition.box_bigStep
