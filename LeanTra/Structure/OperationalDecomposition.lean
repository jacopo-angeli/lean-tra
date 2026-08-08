/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Structure.Derived
public import LeanTra.Confluence.Abstract

/-!
# Operational decomposition

Extends `SRA` with the intro/elim decomposition of the strict compatible
refinement `SRA.scr` and the operational-semantics apparatus it supports:
the value-diagonal `‾Δ`, the elimination-diagonal, the closed-values
relation, the major-slot projection, the one-step evaluation recursor
`aᴱ`, and its Kleene closure `a⇓`.

## Reference

Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
LICS 2026, Definition 5.1, Definition 5.2, Definition 5.5, Definition 5.6.

## Notation warning

In the accompanying PDF the introduction operation carries an OVERLINE
that is invisible to text extraction. Every occurrence of `Δ` inside
the operational-semantics chapter is `‾Δ = intro 1`, NOT the base
identity `Δη = 1`. Here `introDiag` denotes `‾Δ`; the plain `(1 : α)`
is unchanged.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale LeanTra.Confluence

universe u

/-- Operational decomposition on an SRA equipped with a modality: a pair
of weakly unital orthogonal morphisms `intro` (`‾·`) and `elim`
(`⟨·₁, ·₂⟩`) whose joint reach recovers the compatible refinement
`SRA.scr`, distribute (oplax) under relation substitution, and for
which the closure `SRA.box` passes through the elimination's major
slot. -/
class OperationalDecomposition (α : Type u)
    [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
    extends SRA α where
  /-- The constructor slot: `intro a` relates `f(t₁,…,tₙ)` to
  `f(s₁,…,sₙ)` for a constructor symbol `f` with argument vectors
  pairwise `a`-related. -/
  intro : α → α
  /-- The elimination slot with a distinguished major (first) and minor
  (second) argument: `elim a b` relates `f(t₀,…,tₙ)` to `f(s₀,…,sₙ)`
  for a destructor `f` with the major argument pair `a`-related and the
  minor argument vector `b`-related. -/
  elim : α → α → α
  /-- Join preservation of `intro`. -/
  protected intro_sSup (s : Set α) : intro (sSup s) = sSup (intro '' s)
  /-- Composition preservation of `intro`. -/
  protected intro_mul (a b : α) : intro (a * b) = intro a * intro b
  /-- Involution preservation of `intro`. -/
  protected intro_converse (a : α) : intro (aᵒ) = (intro a)ᵒ
  /-- Oplaxness of `intro` at the identity: `‾Δ = intro 1` is
  co-reflexive. -/
  protected intro_one_le : intro 1 ≤ 1
  /-- Join preservation of `elim` in the product-order sense: joins
  taken componentwise on pairs pass under `elim`. -/
  protected elim_sSup (s : Set (α × α)) :
      elim (sSup (Prod.fst '' s)) (sSup (Prod.snd '' s))
        = sSup ((fun p : α × α => elim p.1 p.2) '' s)
  /-- Composition preservation of `elim` in each slot. -/
  protected elim_mul (a a' b b' : α) :
      elim (a * a') (b * b') = elim a b * elim a' b'
  /-- Involution preservation of `elim` in each slot. -/
  protected elim_converse (a b : α) : elim (aᵒ) (bᵒ) = (elim a b)ᵒ
  /-- Oplaxness of `elim` at the identity pair: the elimination-diagonal
  `elim 1 1` is co-reflexive. -/
  protected elim_one_one_le : elim 1 1 ≤ 1
  /-- Orthogonality of `intro` and `elim`: no term is simultaneously
  the image of an `intro`-relation on the left and of an `elim`-relation
  on the right. -/
  protected intro_mul_elim_le_bot (a b c : α) : intro a * elim b c ≤ ⊥
  /-- Decomposition of the compatible refinement into a constructor part
  and a destructor part on the diagonal. -/
  protected scr_eq_intro_sup_elim (a : α) : SRA.scr a = intro a ⊔ elim a a
  /-- Oplax distributivity of substitution over `intro`. -/
  protected subst_intro_le (a b : α) :
      SRA.subst (intro a) b ≤ intro (SRA.subst a b)
  /-- Oplax slot-wise distributivity of substitution over `elim`. -/
  protected subst_elim_le (a₁ a₂ b : α) :
      SRA.subst (elim a₁ a₂) b ≤ elim (SRA.subst a₁ b) (SRA.subst a₂ b)
  /-- `SRA.box` commutes with the elimination through its major slot. -/
  protected box_elim (a b : α) :
      SRA.box (elim a b) = elim (SRA.box a) b

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-- Monotonicity of `intro`, from join preservation on a two-element
subset. -/
theorem intro_mono ⦃a b : α⦄ (h : a ≤ b) :
    OperationalDecomposition.intro a ≤ OperationalDecomposition.intro b := by
  have hsup : a ⊔ b = b := sup_of_le_right h
  have hs := OperationalDecomposition.intro_sSup (α := α) {a, b}
  rw [Set.image_pair, sSup_pair, sSup_pair, hsup] at hs
  exact le_sup_left.trans hs.ge

/-- Monotonicity of `elim` in each slot, from componentwise join
preservation on the two-element pair set `{(a, b), (a', b')}`. -/
theorem elim_mono ⦃a a' b b' : α⦄ (ha : a ≤ a') (hb : b ≤ b') :
    OperationalDecomposition.elim a b ≤ OperationalDecomposition.elim a' b' := by
  have hsup_a : a ⊔ a' = a' := sup_of_le_right ha
  have hsup_b : b ⊔ b' = b' := sup_of_le_right hb
  have h := OperationalDecomposition.elim_sSup (α := α) {(a, b), (a', b')}
  rw [show (Prod.fst '' ({(a, b), (a', b')} : Set (α × α))) = {a, a'} from by
        simp [Set.image_pair],
      show (Prod.snd '' ({(a, b), (a', b')} : Set (α × α))) = {b, b'} from by
        simp [Set.image_pair],
      show ((fun p : α × α => OperationalDecomposition.elim p.1 p.2)
              '' ({(a, b), (a', b')} : Set (α × α)))
            = {OperationalDecomposition.elim a b,
                OperationalDecomposition.elim a' b'} from by
        simp [Set.image_pair],
      sSup_pair, sSup_pair, sSup_pair, hsup_a, hsup_b] at h
  exact le_sup_left.trans h.ge

/-- The major-slot projection `⟨a⟩ := elim a 1`. -/
abbrev maj (a : α) : α := OperationalDecomposition.elim a 1

/-- The value-diagonal `‾Δ := intro 1`. -/
abbrev introDiag : α := OperationalDecomposition.intro 1

/-- The elimination-diagonal `elim 1 1`. -/
abbrev elimDiag : α := OperationalDecomposition.elim 1 1

/-- The closed-values relation `Δᵥ := □ ‾Δ`. -/
def valDiag : α := SRA.box (introDiag : α)

/-- Gentzen Inversion Principle: every `a`-step factors on the left
through an elimination with an introduction form in the major slot. -/
def GIP (a : α) : Prop := a ≤ maj (introDiag : α) * a

/-- Invariance under the value modality: `a` is closed and factors on
the left through the major-slot projection of the closed-values
relation. -/
def Inv (a : α) : Prop := a = SRA.box a ∧ a = maj (valDiag : α) * a

/-- `intro a` lies below the compatible refinement. -/
theorem intro_le_scr (a : α) :
    OperationalDecomposition.intro a ≤ SRA.scr a := by
  rw [OperationalDecomposition.scr_eq_intro_sup_elim]
  exact le_sup_left

/-- The diagonal elimination `elim a a` lies below the compatible
refinement. -/
theorem elim_self_le_scr (a : α) :
    OperationalDecomposition.elim a a ≤ SRA.scr a := by
  rw [OperationalDecomposition.scr_eq_intro_sup_elim]
  exact le_sup_right

/-- Mirror orthogonality: `elim` on the left composes to `⊥` with
`intro` on the right. -/
theorem elim_mul_intro_le_bot (a b c : α) :
    OperationalDecomposition.elim a b * OperationalDecomposition.intro c ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_le_converse_iff,
      IsInvolutiveQuantale.converse_bot,
      IsInvolutiveQuantale.mul_converse,
      ← OperationalDecomposition.intro_converse,
      ← OperationalDecomposition.elim_converse]
  exact OperationalDecomposition.intro_mul_elim_le_bot _ _ _

/-- Idempotence of the value-diagonal under composition. -/
@[simp]
theorem introDiag_mul_self :
    (introDiag : α) * introDiag = introDiag := by
  change OperationalDecomposition.intro 1 * OperationalDecomposition.intro 1
     = OperationalDecomposition.intro 1
  rw [← OperationalDecomposition.intro_mul, mul_one]

/-- Under the Gentzen Inversion Principle, composing an introduction on
the left with a GIP relation on the right lands in `⊥`. -/
theorem intro_mul_of_gip {a : α} (hGIP : GIP a) (x : α) :
    OperationalDecomposition.intro x * a ≤ (⊥ : α) := by
  calc OperationalDecomposition.intro x * a
      ≤ OperationalDecomposition.intro x
          * (maj (introDiag : α) * a) := by
        exact mul_le_mul' le_rfl hGIP
    _ = OperationalDecomposition.intro x
          * maj (introDiag : α) * a := by
        rw [mul_assoc]
    _ ≤ (⊥ : α) * a := by
        refine mul_le_mul' ?_ le_rfl
        change OperationalDecomposition.intro x
              * OperationalDecomposition.elim (introDiag : α) 1 ≤ ⊥
        exact OperationalDecomposition.intro_mul_elim_le_bot _ _ _
    _ = ⊥ := Quantale.bot_mul

/-- The major-slot projection composed with the value-diagonal on the
right lands in `⊥`. -/
theorem maj_mul_introDiag_le_bot (a : α) : maj a * (introDiag : α) ≤ ⊥ := by
  change OperationalDecomposition.elim a 1
     * OperationalDecomposition.intro 1 ≤ ⊥
  exact elim_mul_intro_le_bot _ _ _

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
theorem bigStep_fix (a : α) :
    bigStep a = introDiag ⊔ oneStep a * bigStep a := by
  change (oneStep a)∗ * introDiag = introDiag ⊔ oneStep a * ((oneStep a)∗ * introDiag)
  conv_lhs => rw [LeanTra.Confluence.star_fix]
  rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]

/-- Star-normal-form least-prefix-point law: `a⇓` is below every
prefix point of `x ↦ ‾Δ ⊔ aᴱ * x`. -/
theorem bigStep_le_of {a x : α}
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
the paper's Prop. 29(c) there. The three auxiliary "`□` commutes with"
premises (`hboxIntroDiag`, `hboxOneStep`, `hboxStar`) are likewise not
derivable from the current axioms even under `hmul`, and are carried
explicitly rather than proved. -/
theorem box_bigStep
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

end OperationalDecomposition

#print axioms OperationalDecomposition.intro_mono
#print axioms OperationalDecomposition.elim_mono
#print axioms OperationalDecomposition.intro_le_scr
#print axioms OperationalDecomposition.elim_self_le_scr
#print axioms OperationalDecomposition.elim_mul_intro_le_bot
#print axioms OperationalDecomposition.introDiag_mul_self
#print axioms OperationalDecomposition.intro_mul_of_gip
#print axioms OperationalDecomposition.maj_mul_introDiag_le_bot
#print axioms OperationalDecomposition.evalRec_fix
#print axioms OperationalDecomposition.evalRec_le_of
#print axioms OperationalDecomposition.oneStep_fix
#print axioms OperationalDecomposition.oneStep_le_of
#print axioms OperationalDecomposition.bigStep_fix
#print axioms OperationalDecomposition.bigStep_le_of
#print axioms OperationalDecomposition.box_bigStep
