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
the operational-semantics chapter is `‾Δ = intro 1`, NOT the base
identity `Δη = 1`. Here `introDiag` denotes `‾Δ`; the plain `(1 : α)`
is unchanged.

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

/-- The evaluation-recursor step `x ↦ (‾Δ ⊔ ⟨x⟩) * a`, bundled as an
`OrderHom` for `OrderHom.lfp`. -/
def evalStep (a : α) : α →o α where
  toFun x := ((introDiag : α) ⊔ maj x) * a
  monotone' _ _ h := by
    exact mul_le_mul' (sup_le_sup_left
      (elim_mono h le_rfl) _) le_rfl

/-- The evaluation recursor `aᶠ`: the least fixed point of `evalStep a`. -/
def evalRec (a : α) : α := (evalStep a).lfp

/-- Fixed-point law for `evalRec`. -/
theorem evalRec_fix (a : α) :
    evalRec a = ((introDiag : α) ⊔ maj (evalRec a)) * a := by
  change (evalStep a).lfp = ((introDiag : α) ⊔ maj (evalStep a).lfp) * a
  exact ((evalStep a).map_lfp).symm

/-- Least-prefix-point induction for `evalRec`. -/
theorem evalRec_le_of {a x : α}
    (h : ((introDiag : α) ⊔ maj x) * a ≤ x) : evalRec a ≤ x :=
  (evalStep a).lfp_le h

/-- One-step evaluation `aᴱ := (a ⊔ ‾Δ)ᶠ`. -/
def oneStep (a : α) : α := evalRec (a ⊔ introDiag)

/-- Big-step evaluation `a⇓ := (aᴱ)∗ * ‾Δ`. -/
def bigStep (a : α) : α := (oneStep a)∗ * introDiag

private theorem evalStep_apply_a_sup_introDiag
    {a : α} (hGIP : GIP a) (x : α) :
    ((introDiag : α) ⊔ maj x) * (a ⊔ introDiag)
      = introDiag ⊔ maj x * a := by
  rw [Quantale.mul_sup_distrib, Quantale.sup_mul_distrib,
      Quantale.sup_mul_distrib]
  refine le_antisymm ?_ ?_
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact (intro_mul_of_gip hGIP _).trans bot_le
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
    oneStep a = introDiag ⊔ maj (oneStep a) * a := by
  change evalRec (a ⊔ introDiag) = introDiag ⊔ maj (evalRec (a ⊔ introDiag)) * a
  conv_lhs => rw [evalRec_fix (a ⊔ introDiag)]
  rw [evalStep_apply_a_sup_introDiag hGIP]

/-- Under `GIP a`, one-step evaluation is the least prefix point of
`x ↦ ‾Δ ⊔ ⟨x⟩ * a`. -/
theorem oneStep_le_of {a x : α} (hGIP : GIP a)
    (h : (introDiag : α) ⊔ maj x * a ≤ x) : oneStep a ≤ x := by
  refine evalRec_le_of ?_
  rw [evalStep_apply_a_sup_introDiag hGIP]
  exact h

private theorem introDiag_mul_oneStep
    {a : α} (hGIP : GIP a) :
    (introDiag : α) * oneStep a = introDiag := by
  conv_lhs => rw [oneStep_fix hGIP]
  rw [Quantale.mul_sup_distrib, introDiag_mul_self]
  refine le_antisymm ?_ le_sup_left
  refine sup_le le_rfl ?_
  calc (introDiag : α) * (maj (oneStep a) * a)
      = introDiag * maj (oneStep a) * a := (mul_assoc _ _ _).symm
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.intro 1
              * OperationalDecomposition.elim (oneStep a) 1 ≤ ⊥
        exact OperationalDecomposition.intro_mul_elim_le_bot _ _ _
    _ = ⊥ := Quantale.bot_mul
    _ ≤ introDiag := bot_le

private theorem introDiag_mul_oneStep_star
    {a : α} (hGIP : GIP a) :
    (introDiag : α) * (oneStep a)∗ = introDiag := by
  refine le_antisymm ?_ ?_
  · refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
    refine LeanTra.Confluence.star_le_of ?_
    refine sup_le ?_ ?_
    · exact Quantale.rightMulResiduation_le_iff_mul_le.mpr
        (by rw [mul_one])
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      calc (introDiag : α) * (oneStep a * ((introDiag : α) ⇨ᵣ introDiag))
          = introDiag * oneStep a * (introDiag ⇨ᵣ introDiag) :=
            (mul_assoc _ _ _).symm
        _ = introDiag * (introDiag ⇨ᵣ introDiag) := by
            rw [introDiag_mul_oneStep hGIP]
        _ ≤ introDiag :=
            Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl
  · calc (introDiag : α)
        = introDiag * 1 := (mul_one _).symm
      _ ≤ introDiag * (oneStep a)∗ := by
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
"right GIP" axiom (`a ≤ a * elimDiag`) that the current class does not
carry. -/
theorem bigStep_fix_starNormalForm (a : α) :
    bigStep a = introDiag ⊔ oneStep a * bigStep a := by
  change (oneStep a)∗ * introDiag = introDiag ⊔ oneStep a * ((oneStep a)∗ * introDiag)
  conv_lhs => rw [LeanTra.Confluence.star_fix]
  rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]

/-- Star-normal-form least-prefix-point law: `a⇓` is below every
prefix point of `x ↦ ‾Δ ⊔ aᴱ * x`. -/
theorem bigStep_le_of_starNormalForm {a x : α}
    (h : (introDiag : α) ⊔ oneStep a * x ≤ x) : bigStep a ≤ x := by
  have hintroDiag : (introDiag : α) ≤ x := le_sup_left.trans h
  have hone : oneStep a * x ≤ x := le_sup_right.trans h
  calc bigStep a
      = (oneStep a)∗ * introDiag := rfl
    _ ≤ (oneStep a)∗ * x := by
        exact mul_le_mul' le_rfl hintroDiag
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
premises (`hboxIntroDiag`, `hboxOneStep`, `hboxStar`) are likewise not
derivable from the current axioms even under `hmul`, and are carried
explicitly rather than proved. -/
theorem box_bigStep_of_box_mul_le
    (hmul : ∀ A B : α, SRA.box (A * B) ≤ SRA.box A * SRA.box B)
    (a : α)
    (hboxIntroDiag : SRA.box (introDiag : α) = introDiag)
    (hboxOneStep : SRA.box (oneStep a) = oneStep (SRA.box a))
    (hboxStar : ∀ b : α, SRA.box (b∗) = (SRA.box b)∗) :
    SRA.box (bigStep a) = bigStep (SRA.box a) := by
  refine le_antisymm ?_ ?_
  · calc SRA.box (bigStep a)
        = SRA.box ((oneStep a)∗ * introDiag) := rfl
      _ ≤ SRA.box ((oneStep a)∗) * SRA.box introDiag := hmul _ _
      _ = (SRA.box (oneStep a))∗ * SRA.box introDiag := by rw [hboxStar]
      _ = (oneStep (SRA.box a))∗ * SRA.box introDiag := by rw [hboxOneStep]
      _ = (oneStep (SRA.box a))∗ * introDiag := by rw [hboxIntroDiag]
      _ = bigStep (SRA.box a) := rfl
  · calc bigStep (SRA.box a)
        = (oneStep (SRA.box a))∗ * introDiag := rfl
      _ = (oneStep (SRA.box a))∗ * SRA.box introDiag := by rw [hboxIntroDiag]
      _ = (SRA.box (oneStep a))∗ * SRA.box introDiag := by rw [hboxOneStep]
      _ = SRA.box ((oneStep a)∗) * SRA.box introDiag := by rw [hboxStar]
      _ ≤ SRA.box ((oneStep a)∗ * introDiag) := SRA.box_mul_box_le _ _
      _ = SRA.box (bigStep a) := rfl

/-- `bigStep a` is idempotent under composition:
`bigStep a * bigStep a = bigStep a`, under `GIP a`. From
`introDiag_mul_oneStep_star hGIP` (`introDiag * (oneStep a)∗ = introDiag`)
and `introDiag_mul_self`. Consumed by `F3` and later by `F6`, `F10`, `F11`. -/
theorem bigStep_mul_self {a : α} (hGIP : GIP a) :
    bigStep a * bigStep a = bigStep a := by
  change (oneStep a)∗ * introDiag * ((oneStep a)∗ * introDiag) = (oneStep a)∗ * introDiag
  rw [mul_assoc ((oneStep a)∗) introDiag ((oneStep a)∗ * introDiag),
      ← mul_assoc introDiag ((oneStep a)∗) introDiag,
      introDiag_mul_oneStep_star hGIP,
      introDiag_mul_self]

/-- Law (5.7a): `SRA.box (oneStep a) = oneStep (SRA.box a)`.

**Status.** As a proof attempt, this is stuck. The `≥` direction is where
the informal argument fails: `oneStep (box a) ≥ introDiag * introDiag =
introDiag` from `evalRec_fix`, while `box (oneStep a) ≤ oneStep a`
factors through `box` which strips to closed-endpoint pairs; the residual
inclusion `introDiag ≤ box (oneStep a)` unwinds to `introDiag ≤ box
introDiag = valDiag`, an inequality of the same shape as the strict
`box`-over-composition inequality refuted in the term model by
`LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box` (that
refutation is at a different subject, not directly at `introDiag`; hence
this is treated as a failed proof attempt, not a formal refutation, per
Phase 5).

No `OperationalDecomposition` instance exists on `SynRel` in this
repository, so `oneStep` and `introDiag` are not available there for a
first-order refutation. Left as `sorry`. -/
theorem box_oneStep (a : α) : SRA.box (oneStep a) = oneStep (SRA.box a) := by
  sorry

/-- Weak form of `box_oneStep`: closedness of the rule propagates to
`oneStep`.

**Status.** As stated (`oneStep a = box (oneStep a)`), the equality also
fails: `oneStep a ≥ introDiag`, `box (oneStep a) ≤ oneStep a`, and the
inclusion `introDiag ≤ box (oneStep a)` factors through the same refuted
`introDiag ≤ box introDiag`. The tools listed in the task (`box_elim`,
`box_sup`, `box_mul_box_le`, `box_le`, `SRA.box_lfp`) suffice to reduce
the goal to that inclusion, at which point the strict half of `box` is
needed. Left as `sorry`. -/
theorem oneStep_isClosed {a : α} (hGIP : GIP a) (h : a = SRA.box a) :
    oneStep a = SRA.box (oneStep a) := by
  sorry

/-- Law (5.7b): `bigStep a = introDiag ⊔ maj (bigStep a) * a * bigStep a`.

**Status.** Under `GIP a`: `bigStep_fix_starNormalForm` plus `oneStep_fix
hGIP` plus `introDiag_mul_oneStep_star hGIP` reduces to
`bigStep a = introDiag ⊔ maj (oneStep a) * a * bigStep a`. The remaining
step `maj (oneStep a) * a * bigStep a = maj (bigStep a) * a * bigStep a`
requires either direction of `oneStep a ≤ bigStep a` or
`bigStep a ≤ oneStep a`, and neither is derivable under `GIP a` alone
(`bigStep a = (oneStep a)∗ * introDiag`, and neither
`oneStep a ≤ (oneStep a)∗ * introDiag` nor its reverse follows from Kleene
star laws without a `1 ≤ introDiag` fact that would collapse `introDiag`
to the unit — precisely the strict half that is refuted). -/
theorem bigStep_fix (a : α) (hGIP : GIP a) :
    bigStep a = introDiag ⊔ maj (bigStep a) * a * bigStep a := by
  sorry

/-- Law (5.7c): if `introDiag ⊔ maj x * a * x ≤ x` then `bigStep a ≤ x`.

**Status.** Under `GIP a`: `bigStep_le_of_starNormalForm` needs
`introDiag ⊔ oneStep a * x ≤ x`. Reducing via `oneStep_fix hGIP` and the
hypothesis needs `maj (oneStep a) * a * x ≤ maj x * a * x`, i.e.
`oneStep a ≤ x`. `oneStep_le_of hGIP` reduces that to `introDiag ⊔ maj x
* a ≤ x`. The hypothesis only gives `maj x * a * x ≤ x`, which yields
`maj x * a ≤ x` only under `1 ≤ x` — not derivable from the hypothesis
alone. -/
theorem bigStep_le_of {a x : α} (hGIP : GIP a)
    (h : introDiag ⊔ maj x * a * x ≤ x) : bigStep a ≤ x := by
  sorry

/-- Law (5.7d): `SRA.box (bigStep a) = bigStep (SRA.box a)`.

**Status.** Same failure mode as `box_oneStep`: `bigStep (box a) ≥
introDiag`, `box (bigStep a) ≤ bigStep a`, and `introDiag ≤ box (bigStep
a)` needs the strict half. Kept as `sorry` per Phase 2; the strictly
weaker `bigStep_isClosed` below is provided alongside. -/
theorem box_bigStep (a : α) : SRA.box (bigStep a) = bigStep (SRA.box a) := by
  sorry

/-- Weak form of `box_bigStep`: closedness of the rule propagates to
`bigStep`.

**Status.** As stated (`bigStep a = box (bigStep a)`), the equality fails
because `bigStep a = (oneStep a)∗ * introDiag ≥ introDiag` while `box
(bigStep a) ≤ bigStep a` can only exceed `box introDiag = valDiag`. The
same `introDiag ≤ box introDiag` is needed and refuted. `box_lfp` applied
to `evalStep` runs into the strict half of `box` over composition, also
refuted. Left as `sorry`. -/
theorem bigStep_isClosed {a : α} (hGIP : GIP a) (h : a = SRA.box a) :
    bigStep a = SRA.box (bigStep a) := by
  sorry

/-- Law (5.7e): if `a = SRA.box a` then
`bigStep a = valDiag ⊔ maj (bigStep a) * a * bigStep a`.

**Status.** Under `GIP a + closedness`: reducing via
`bigStep_fix_starNormalForm` and the intended `bigStep_isClosed` still
requires bridging `introDiag ⇝ valDiag` on the constant summand, which
`bigStep_isClosed` (also open, same refutation) would deliver via
`bigStep a = box (bigStep a)` combined with `introDiag ≤ bigStep a`. The
chain `introDiag ≤ bigStep a = box (bigStep a) ⇒ introDiag ≤ box (bigStep
a)` — followed by the intended `⇒ box introDiag = valDiag ≤ …` — meets
the same refuted `introDiag ≤ box introDiag`. -/
theorem bigStep_fix_of_closed {a : α} (hGIP : GIP a) (h : a = SRA.box a) :
    bigStep a = valDiag ⊔ maj (bigStep a) * a * bigStep a := by
  sorry

/-! ### Structural consequences of the star-normal form

The following two facts are unconditional (no `GIP`, no closedness): they
say `introDiag` sits below `bigStep a` and hence below the deterministic
composite `(bigStep a)ᵒ * bigStep a`. Together they give
`determinism_implies_introDiag_le_valDiag`: the determinism conclusion
`(bigStep a)ᵒ * bigStep a ≤ valDiag` forces `introDiag ≤ valDiag`, i.e.
the strict half of `box` that is refuted in the term model. -/

/-- `introDiag ≤ bigStep a`. Direct consequence of
`bigStep_fix_starNormalForm`. -/
theorem introDiag_le_bigStep (a : α) : (introDiag : α) ≤ bigStep a := by
  conv_rhs => rw [bigStep_fix_starNormalForm]
  exact le_sup_left

/-- `introDiag ≤ (bigStep a)ᵒ * bigStep a`. Combines
`introDiag_le_bigStep` with self-converse `introDiagᵒ = introDiag` (from
`intro_converse` and `converse_one`) and `introDiag * introDiag =
introDiag`. -/
theorem introDiag_le_converse_mul (a : α) :
    (introDiag : α) ≤ (bigStep a)ᵒ * bigStep a := by
  have h_le : (introDiag : α) ≤ bigStep a := introDiag_le_bigStep a
  have h_self : (introDiag : α)ᵒ = introDiag := by
    change (OperationalDecomposition.intro (1 : α))ᵒ
        = OperationalDecomposition.intro 1
    rw [← OperationalDecomposition.intro_converse,
        IsInvolutiveQuantale.converse_one]
  have h_conv : (introDiag : α) ≤ (bigStep a)ᵒ := by
    have := IsInvolutiveQuantale.converse_le_converse h_le
    rwa [h_self] at this
  calc (introDiag : α)
      = introDiag * introDiag := introDiag_mul_self.symm
    _ ≤ (bigStep a)ᵒ * bigStep a := mul_le_mul' h_conv h_le

/-- The determinism conclusion `(bigStep a)ᵒ * bigStep a ≤ valDiag` forces
`introDiag ≤ valDiag`, i.e. the strict half of `box` at `intro 1` that is
refuted by the term-model witness for
`SynRel.not_box_mul_le_mul_box`-style refutations. -/
theorem determinism_implies_introDiag_le_valDiag {a : α}
    (h : (bigStep a)ᵒ * bigStep a ≤ valDiag) :
    (introDiag : α) ≤ valDiag :=
  (introDiag_le_converse_mul a).trans h

end OperationalDecomposition

#print axioms OperationalDecomposition.bigStep_fix_starNormalForm
#print axioms OperationalDecomposition.box_bigStep_of_box_mul_le
#print axioms OperationalDecomposition.bigStep_mul_self

#print axioms OperationalDecomposition.box_oneStep
#print axioms OperationalDecomposition.oneStep_isClosed
#print axioms OperationalDecomposition.bigStep_fix
#print axioms OperationalDecomposition.bigStep_le_of
#print axioms OperationalDecomposition.box_bigStep
#print axioms OperationalDecomposition.bigStep_isClosed
#print axioms OperationalDecomposition.bigStep_fix_of_closed
#print axioms OperationalDecomposition.introDiag_le_bigStep
#print axioms OperationalDecomposition.introDiag_le_converse_mul
#print axioms OperationalDecomposition.determinism_implies_introDiag_le_valDiag
