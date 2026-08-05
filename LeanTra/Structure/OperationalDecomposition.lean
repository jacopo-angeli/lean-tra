/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Structure.Derived
public import LeanTra.Confluence.Abstract

/-!
# Operational decomposition

Extension of the SRA class layering the operational-semantics apparatus
of the extended draft's Chapter 5. Splits the strict compatible
refinement `SRA.scr` into a *constructor* part `intro` and a
*destructor* part `elim` with a distinguished *major* slot; derives the
values relation `valDiag`, the one-step recursor, and the big-step
evaluation.

## Notation warning

In the extended-draft PDF, the introduction operation carries an
OVERLINE — drawn as a rule and invisible to text extraction. Every
occurrence of `Δ` inside the operational-semantics chapter of the
paper is `‾Δ = intro 1`, NOT the identity `Δη = 1` of the base SRA.
Here we use `introDiag` for that overlined `‾Δ`, strictly following the
paper's rule; the plain identity `(1 : α)` is unchanged.

## Class (draft Def. 5.1)

`class OperationalDecomposition α extends SRA α` with

* `intro : α → α`, `elim : α → α → α` — the two operations;
* homomorphism laws for `intro` and `elim` in composition and converse,
  each oplax on the unit;
* mutual orthogonality `intro _ * elim _ _ ≤ ⊥`;
* decomposition `SRA.scr a = intro a ⊔ elim a a`;
* substitution distributes over `intro` and `elim` (oplax);
* modality-eliminates-major: `SRA.box (elim a b) ≤ elim (SRA.box a) b`.

## Derived data (never fields)

* `maj a := elim a 1` — the "major slot" projection;
* `introDiag := intro 1` — the value-diagonal `‾Δ`;
* `elimDiag := elim 1 1` — the elimination-diagonal;
* `valDiag := SRA.box introDiag` — closed values (denoted `Δᵥ` in the
  paper).

## Predicates (never fields)

* `GIP a := a ≤ elimDiag * a` — Gentzen Inversion Principle;
* `Inv a := a = maj valDiag * a` — invariance under the value modality.

Every theorem needing `GIP` or `Inv` takes it as an explicit hypothesis.

## Contents

* The class, with a docstring on every field citing the paper reading
  on syntactic terms.
* Derived data and the two predicates.
* Service lemmas (task 3): `intro_le_scr`, `elim_self_le_scr`,
  `elim_mul_intro_le_bot` (mirror orthogonality, by converse; copies
  the `scr_mul_varDiag_le_bot` template), `introDiag_mul_self`,
  `intro_mul_of_gip`, `maj_mul_introDiag_le_bot`.
* Recursor (task 5), mirroring `howeStep` / `howe` from
  `Structure/Derived.lean`: `evalStep`, `evalRec`, `evalRec_fix`,
  `evalRec_le_of`, `oneStep := evalRec (a ⊔ introDiag)`,
  `bigStep := (oneStep a)∗ * introDiag`.
* Prop. 29(a) `oneStep_fix`, `oneStep_le_of`: `oneStep a` is the least
  solution of `x = introDiag ⊔ maj x * a`, under `GIP a`. Proof
  follows the draft: expand `(introDiag ⊔ maj x) * (a ⊔ introDiag)`
  into four summands and discard two via the service lemmas.
* Prop. 29(b) `bigStep_fix`, `bigStep_le_of` (star-normal form) —
  see the block-level docstring for the deviation from the draft's
  precise statement and why.
* Prop. 29(c) `box_bigStep`, hypothesis-carrying: takes the refuted
  `∀ A B, SRA.box (A * B) ≤ SRA.box A * SRA.box B` as an explicit
  hypothesis `hmul` (plus three auxiliary "`SRA.box` commutes with"
  hypotheses that themselves are not derivable from the current axioms
  even under `hmul` — see the block above the theorem for the honest
  attempt at fixed-point induction directly on the recursor and where
  it stalls).

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  Extended draft (Chapter 5) accompanying the LICS 2026 paper.
  Def. 5.1 and Prop. 29. Notation warning above is verified against
  the PDF glyphs.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale LeanTra.Confluence

universe u

/-- Extension of `SRA` with the intro/elim decomposition of the strict
compatible refinement, following the extended draft's Def. 5.1. Every
axiom is a paper axiom; nothing here is a derived law. -/
class OperationalDecomposition (α : Type u)
    [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
    extends SRA α where
  /-- Constructor slot. On syntactic terms, `intro a` relates
  `f(t₁,…,tₙ)` to `f(s₁,…,sₙ)` when `f` is a constructor symbol and the
  argument vectors are pairwise `a`-related. (Draft Def. 5.1, `‾i`.) -/
  intro : α → α
  /-- Elimination slot with a distinguished major (first) and minor
  (second) position. On syntactic terms, `elim a b` relates
  `f(t₀,…,tₙ)` to `f(s₀,…,sₙ)` when `f` is a destructor with the major
  argument pair `a`-related and the minor argument vector `b`-related.
  (Draft Def. 5.1, `‾e⟨·,·⟩`.) -/
  elim : α → α → α
  /-- Monotonicity of `intro`. -/
  protected intro_mono ⦃a b : α⦄ : a ≤ b → intro a ≤ intro b
  /-- `intro` preserves composition slot-wise: constructor-refining a
  composite is the composite of the constructor-refinements. -/
  protected intro_mul (a b : α) : intro (a * b) = intro a * intro b
  /-- `intro` preserves converse: swapping the endpoints of a
  constructor-refinement is the constructor-refinement of the swapped
  relation. -/
  protected intro_converse (a : α) : intro (aᵒ) = (intro a)ᵒ
  /-- `intro` is oplax on the unit: `intro 1 ≤ 1`. In terms this says
  the value-diagonal `‾Δ = intro 1` is coreflexive. -/
  protected intro_one_le : intro 1 ≤ 1
  /-- Monotonicity of `elim` in both slots. -/
  protected elim_mono ⦃a a' b b' : α⦄ : a ≤ a' → b ≤ b' →
      elim a b ≤ elim a' b'
  /-- `elim` preserves composition slot-wise. -/
  protected elim_mul (a a' b b' : α) :
      elim (a * a') (b * b') = elim a b * elim a' b'
  /-- `elim` preserves converse slot-wise. -/
  protected elim_converse (a b : α) : elim (aᵒ) (bᵒ) = (elim a b)ᵒ
  /-- `elim` is oplax on the identity pair: `elim 1 1 ≤ 1`. -/
  protected elim_one_one_le : elim 1 1 ≤ 1
  /-- Constructors and destructors are disjoint under composition: no
  term is simultaneously the image of an `intro`-relation on the left
  and of an `elim`-relation on the right. (Draft Def. 5.1,
  orthogonality clause.) -/
  protected intro_mul_elim_le_bot (a b c : α) : intro a * elim b c ≤ ⊥
  /-- The compatibility-refinement decomposition:
  `scr a = intro a ⊔ elim a a`. The right-hand side is "constructor
  refinement of `a` OR destructor refinement with `a` in every slot",
  which recovers the compatible-refinement of `a`. -/
  protected scr_eq_intro_sup_elim (a : α) : SRA.scr a = intro a ⊔ elim a a
  /-- Substitution distributes (oplax) over `intro`. -/
  protected subst_intro_le (a b : α) :
      SRA.subst (intro a) b ≤ intro (SRA.subst a b)
  /-- Substitution distributes (oplax, slot-wise) over `elim`. -/
  protected subst_elim_le (a₁ a₂ b : α) :
      SRA.subst (elim a₁ a₂) b ≤ elim (SRA.subst a₁ b) (SRA.subst a₂ b)
  /-- Modality eliminates through the major slot: closing the two
  endpoints of an `elim` relation only closes the major-slot argument.
  This is the "major arguments of a closed term are closed"
  distributivity of `SRA.box`. -/
  protected box_elim_le (a b : α) :
      SRA.box (elim a b) ≤ elim (SRA.box a) b

namespace OperationalDecomposition

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
  [IsInvolutiveQuantale α] [OperationalDecomposition α]

/-! ## Derived data (task 2)

Declared `abbrev` (not `def`) so that Lean's elaborator unfolds them in
subsequent definitional checks; the `evalStep` recursor below uses
`maj` and `introDiag` inside its `toFun`, and needs the unfold to line
up with `intro` and `elim` at the `map_lfp` step. -/

/-- The major-slot projection `⟨·⟩ := elim · 1`. -/
abbrev maj (a : α) : α := OperationalDecomposition.elim a 1

/-- The value-diagonal `‾Δ := intro 1` (paper's overlined `Δ`). -/
abbrev introDiag : α := OperationalDecomposition.intro 1

/-- The elimination-diagonal `elim 1 1`. -/
abbrev elimDiag : α := OperationalDecomposition.elim 1 1

/-- The closed-values relation `Δᵥ := SRA.box (intro 1)`. -/
def valDiag : α := SRA.box (introDiag : α)

/-- Gentzen Inversion Principle: `a ≤ elimDiag * a`. Every `a`-step
factors through the elimination-diagonal on the left. NOT a field;
theorems consuming it take it as an explicit hypothesis. -/
def GIP (a : α) : Prop := a ≤ elimDiag * a

/-- Invariance under the value modality: `a = maj valDiag * a`. NOT a
field; theorems consuming it take it as an explicit hypothesis. -/
def Inv (a : α) : Prop := a = maj (valDiag : α) * a

/-! ## Service lemmas (task 3) -/

/-- `intro a ≤ scr a`. Immediate from `scr = intro ⊔ elim aa`. -/
theorem intro_le_scr (a : α) :
    OperationalDecomposition.intro a ≤ SRA.scr a := by
  rw [OperationalDecomposition.scr_eq_intro_sup_elim]
  exact le_sup_left

/-- `elim a a ≤ scr a`. Immediate from `scr = intro ⊔ elim aa`. -/
theorem elim_self_le_scr (a : α) :
    OperationalDecomposition.elim a a ≤ SRA.scr a := by
  rw [OperationalDecomposition.scr_eq_intro_sup_elim]
  exact le_sup_right

/-- Mirror orthogonality: `elim a b * intro c ≤ ⊥`. Derived from the
axiomatic `intro _ * elim _ _ ≤ ⊥` via converse, copying the
`scr_mul_varDiag_le_bot` template from `Structure/Derived.lean`. -/
theorem elim_mul_intro_le_bot (a b c : α) :
    OperationalDecomposition.elim a b * OperationalDecomposition.intro c ≤ ⊥ := by
  rw [← IsInvolutiveQuantale.converse_le_converse_iff,
      IsInvolutiveQuantale.converse_bot,
      IsInvolutiveQuantale.mul_converse,
      ← OperationalDecomposition.intro_converse,
      ← OperationalDecomposition.elim_converse]
  exact OperationalDecomposition.intro_mul_elim_le_bot _ _ _

/-- Idempotence of the value-diagonal: `introDiag * introDiag = introDiag`.
From `intro_mul` at `1 * 1 = 1`. -/
@[simp]
theorem introDiag_mul_self :
    (introDiag : α) * introDiag = introDiag := by
  change OperationalDecomposition.intro 1 * OperationalDecomposition.intro 1
     = OperationalDecomposition.intro 1
  rw [← OperationalDecomposition.intro_mul, mul_one]

/-- `intro`-then-`GIP` annihilation: under `GIP a`, `intro x * a ≤ ⊥`
for every `x`. From `a ≤ elimDiag * a` (GIP) and the mirror
`intro _ * elim _ _ ≤ ⊥`. -/
theorem intro_mul_of_gip {a : α} (hGIP : GIP a) (x : α) :
    OperationalDecomposition.intro x * a ≤ (⊥ : α) := by
  calc OperationalDecomposition.intro x * a
      ≤ OperationalDecomposition.intro x * (elimDiag * a) := by
        exact mul_le_mul' le_rfl hGIP
    _ = OperationalDecomposition.intro x * elimDiag * a := by
        rw [mul_assoc]
    _ ≤ (⊥ : α) * a := by
        exact mul_le_mul' (OperationalDecomposition.intro_mul_elim_le_bot _ _ _) le_rfl
    _ = ⊥ := Quantale.bot_mul

/-- `maj a * introDiag ≤ ⊥`. Instance of the mirror orthogonality
`elim_mul_intro_le_bot` at (major, minor, argument) `(a, 1, 1)`. -/
theorem maj_mul_introDiag_le_bot (a : α) : maj a * (introDiag : α) ≤ ⊥ := by
  change OperationalDecomposition.elim a 1
     * OperationalDecomposition.intro 1 ≤ ⊥
  exact elim_mul_intro_le_bot _ _ _

/-! ## Recursor (task 5) -/

/-- The evaluation recursor step: `x ↦ (introDiag ⊔ maj x) * a`. Bundled
as an `OrderHom` so its least fixed point can be taken via
`OrderHom.lfp`. Direct analogue of `SRA.howeStep`. -/
def evalStep (a : α) : α →o α where
  toFun x := ((introDiag : α) ⊔ maj x) * a
  monotone' _ _ h := by
    exact mul_le_mul' (sup_le_sup_left
      (OperationalDecomposition.elim_mono h le_rfl) _) le_rfl

/-- The evaluation recursor `·ᶠ`: least solution of
`x = (introDiag ⊔ maj x) * a`, via Knaster–Tarski. -/
def evalRec (a : α) : α := (evalStep a).lfp

/-- Fixed-point law for the evaluation recursor. -/
theorem evalRec_fix (a : α) :
    evalRec a = ((introDiag : α) ⊔ maj (evalRec a)) * a := by
  change (evalStep a).lfp = ((introDiag : α) ⊔ maj (evalStep a).lfp) * a
  exact ((evalStep a).map_lfp).symm

/-- Fixed-point induction for the evaluation recursor. -/
theorem evalRec_le_of {a x : α}
    (h : ((introDiag : α) ⊔ maj x) * a ≤ x) : evalRec a ≤ x :=
  (evalStep a).lfp_le h

/-- One-step evaluation `aᴱ := (a ⊔ ‾Δ)ᶠ` (draft Def. 27). -/
def oneStep (a : α) : α := evalRec (a ⊔ introDiag)

/-- Big-step evaluation `a⇓ := (aᴱ)∗ * ‾Δ` (draft Def. 28). -/
def bigStep (a : α) : α := (oneStep a)∗ * introDiag

/-! ## Prop. 29(a) — `oneStep` characterisation under `GIP a` (task 6) -/

/-- Expansion lemma for the four-summand argument of Prop. 29(a).
Under `GIP a`, `(introDiag ⊔ maj x) * (a ⊔ introDiag)` collapses to
`introDiag ⊔ maj x * a`: two of the four summands (`introDiag * a` via
`intro_mul_of_gip`, and `maj x * introDiag` via
`maj_mul_introDiag_le_bot`) are `≤ ⊥`, `introDiag * introDiag = introDiag`,
and the last summand `maj x * a` is kept as-is. -/
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

/-- Prop. 29(a) fixed-point law: under `GIP a`, `oneStep a` satisfies
`oneStep a = introDiag ⊔ maj (oneStep a) * a`. Proof: unfold `oneStep`,
apply `evalRec_fix`, and rewrite the RHS via
`evalStep_apply_a_sup_introDiag`. -/
theorem oneStep_fix {a : α} (hGIP : GIP a) :
    oneStep a = introDiag ⊔ maj (oneStep a) * a := by
  change evalRec (a ⊔ introDiag) = introDiag ⊔ maj (evalRec (a ⊔ introDiag)) * a
  conv_lhs => rw [evalRec_fix (a ⊔ introDiag)]
  rw [evalStep_apply_a_sup_introDiag hGIP]

/-- Prop. 29(a) least-solution: under `GIP a`, `oneStep a` is below
every prefix point of `x ↦ introDiag ⊔ maj x * a`. -/
theorem oneStep_le_of {a x : α} (hGIP : GIP a)
    (h : (introDiag : α) ⊔ maj x * a ≤ x) : oneStep a ≤ x := by
  refine evalRec_le_of ?_
  rw [evalStep_apply_a_sup_introDiag hGIP]
  exact h

/-! ## Prop. 29(b) — `bigStep` characterisation (task 7)

We prove the **star-normal form** of Prop. 29(b):

* `bigStep_fix` — `bigStep a = introDiag ⊔ oneStep a * bigStep a` (under
  `GIP a`);
* `bigStep_le_of` — `(introDiag ⊔ oneStep a * x ≤ x) → bigStep a ≤ x`
  (unconditional).

both via `star_fix` and `star_le_of` from `Confluence/Abstract.lean`, as
task 7 prescribes.

**Deviation from the draft's exact form.** The draft states Prop. 29(b)
as "`bigStep a` is the least solution of `x = introDiag ⊔ maj x * a * x`"
(with `maj x` on the RHS, `x` being the fixed-point variable). Reducing
the star-normal form to that exact form requires the extra rewrite

  `oneStep a * bigStep a = maj (bigStep a) * a * bigStep a`,

i.e. replacing `maj (oneStep a)` by `maj (bigStep a)` in
`bigStep_fix`'s RHS. That step needs either `oneStep a ≤ bigStep a`
(which fails: `bigStep a` ends with `* introDiag`, so it is not
`≥ oneStep a` unless `1 ≤ introDiag`, which forces `introDiag = 1` and
collapses the modality) OR a "right GIP" axiom `a ≤ a * elimDiag`
(which the current class does not provide). See the docstring of
`box_bigStep` for the downstream consequence. The star-normal form is
what the modality-transfer argument (task 8) actually consumes. -/

/-- `introDiag * oneStep a = introDiag`. From `intro_mul_elim_le_bot`
(killing `introDiag * maj (oneStep a)`) and `introDiag_mul_self`. -/
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

/-- `introDiag * (oneStep a)∗ = introDiag`. Star induction on `oneStep a`
against the target `introDiag ⇨ᵣ introDiag`, using
`introDiag_mul_oneStep` for the inductive step. -/
private theorem introDiag_mul_oneStep_star
    {a : α} (hGIP : GIP a) :
    (introDiag : α) * (oneStep a)∗ = introDiag := by
  refine le_antisymm ?_ ?_
  · -- Right residual: `introDiag * y ≤ introDiag ↔ y ≤ introDiag ⇨ᵣ introDiag`.
    refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
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

/-- Prop. 29(b) fixed-point law (star-normal form):
`bigStep a = introDiag ⊔ oneStep a * bigStep a`. Uses `star_fix` and
associativity; no `GIP a` hypothesis needed at this level. -/
theorem bigStep_fix (a : α) :
    bigStep a = introDiag ⊔ oneStep a * bigStep a := by
  change (oneStep a)∗ * introDiag = introDiag ⊔ oneStep a * ((oneStep a)∗ * introDiag)
  conv_lhs => rw [LeanTra.Confluence.star_fix]
  rw [Quantale.sup_mul_distrib, one_mul, mul_assoc]

/-- Prop. 29(b) least-solution (star-normal form): `bigStep a` is below
every prefix point of `x ↦ introDiag ⊔ oneStep a * x`. Standard star
induction: `(oneStep a)∗ * introDiag ≤ x` follows from `introDiag ≤ x`
(the first half of the hypothesis) and `oneStep a * x ≤ x` (the second
half) transported through the left residual. No hypothesis on `a`
needed. -/
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

/-! ## Prop. 29(c) — `box (bigStep a) = bigStep (box a)` (task 8)

STOP HERE. The equality between `SRA.box (bigStep a)` and
`bigStep (SRA.box a)` requires

  `SRA.box (A * B) ≤ SRA.box A * SRA.box B`         (*)

which is REFUTED in the context-indexed term model
(`LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`). We
state `box_bigStep` hypothesis-carrying, taking (*) as `hmul`.

**Honest attempt without `hmul`, by fixed-point induction directly on
the recursor rather than through `SRA.box_lfp`.** The strategy would
be: show `bigStep (SRA.box a)` is a prefix point of
`x ↦ introDiag ⊔ oneStep (SRA.box a) * x` (immediate from
`bigStep_fix`), and separately show `SRA.box (bigStep a)` is bounded
above and below via `bigStep_le_of`.

The lax `SRA.box_mul_box_le : SRA.box A * SRA.box B ≤ SRA.box (A * B)`
DOES close one direction. Specifically it lets us prove
`bigStep (SRA.box a) ≤ SRA.box (bigStep a)`, provided the auxiliary
identities `SRA.box (oneStep a) = oneStep (SRA.box a)` and
`SRA.box (b∗) = (SRA.box b)∗` and `SRA.box introDiag = introDiag`
hold. Each of those is itself an instance of `SRA.box` commuting with
a fixed point (recursor, star, or constant) — for `introDiag` we would
need `SRA.box (intro a) ≤ intro (SRA.box a)`, an axiom the class does
NOT provide (only `box_elim_le` is given).

The *other* direction, `SRA.box (bigStep a) ≤ bigStep (SRA.box a)`,
is the one that needs `SRA.box (A * B) ≤ SRA.box A * SRA.box B` at
every unfolding of the star: to move `SRA.box` past a `*` in
`(oneStep a)∗ * introDiag`, we need to split
`SRA.box ((oneStep a)∗ * introDiag)` into
`SRA.box (oneStep a)∗ * SRA.box introDiag`, which is exactly the
refuted lax direction. Without (*), the derivation stalls at that
step and cannot be recovered by any choice of prefix point on the
recursor.

**Point of failure of the direct approach.** In the `bigStep_le_of`
route: to apply `bigStep_le_of` to `SRA.box (bigStep a) ≤ target`, we
need to bring the outer `SRA.box` past the outer `*` inside the
definition of `bigStep`, at which point exactly the refuted
`SRA.box (A * B) ≤ SRA.box A * SRA.box B` is invoked.

Conclusion: **the lax `box_mul_box_le` closes at most one of the two
inequalities**, and the missing direction is exactly the refuted one.
The hypothesis-carrying formulation below is therefore the minimal
statement that closes; no `sorry`, no class field. -/

/-- Prop. 29(c) hypothesis-carrying. Takes as explicit assumptions

* `hmul` — the direction `SRA.box (A * B) ≤ SRA.box A * SRA.box B`
  that is refuted in the term model
  (`LeanTra.Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`);
* `hboxIntroDiag`, `hboxOneStep`, `hboxStar` — three "`SRA.box`
  commutes with" hypotheses that are not derivable from the current
  axioms even under `hmul` (see the block-level docstring above).

Under these, `SRA.box` commutes with `bigStep`. Route: rewrite
`SRA.box ((oneStep a)∗ * introDiag)` past the outer `*` via `hmul`
(the refuted direction) for `≤`, and past the outer `*` via
`SRA.box_mul_box_le` (the lax theorem) for `≥`. -/
theorem box_bigStep
    (hmul : ∀ A B : α, SRA.box (A * B) ≤ SRA.box A * SRA.box B)
    (a : α)
    (hboxIntroDiag : SRA.box (introDiag : α) = introDiag)
    (hboxOneStep : SRA.box (oneStep a) = oneStep (SRA.box a))
    (hboxStar : ∀ b : α, SRA.box (b∗) = (SRA.box b)∗) :
    SRA.box (bigStep a) = bigStep (SRA.box a) := by
  refine le_antisymm ?_ ?_
  · -- `SRA.box (bigStep a) ≤ bigStep (SRA.box a)` uses `hmul`.
    calc SRA.box (bigStep a)
        = SRA.box ((oneStep a)∗ * introDiag) := rfl
      _ ≤ SRA.box ((oneStep a)∗) * SRA.box introDiag := hmul _ _
      _ = (SRA.box (oneStep a))∗ * SRA.box introDiag := by rw [hboxStar]
      _ = (oneStep (SRA.box a))∗ * SRA.box introDiag := by rw [hboxOneStep]
      _ = (oneStep (SRA.box a))∗ * introDiag := by rw [hboxIntroDiag]
      _ = bigStep (SRA.box a) := rfl
  · -- `bigStep (SRA.box a) ≤ SRA.box (bigStep a)` uses only the lax
    -- `SRA.box_mul_box_le`.
    calc bigStep (SRA.box a)
        = (oneStep (SRA.box a))∗ * introDiag := rfl
      _ = (oneStep (SRA.box a))∗ * SRA.box introDiag := by rw [hboxIntroDiag]
      _ = (SRA.box (oneStep a))∗ * SRA.box introDiag := by rw [hboxOneStep]
      _ = SRA.box ((oneStep a)∗) * SRA.box introDiag := by rw [hboxStar]
      _ ≤ SRA.box ((oneStep a)∗ * introDiag) := SRA.box_mul_box_le _ _
      _ = SRA.box (bigStep a) := rfl

end OperationalDecomposition

#print axioms OperationalDecomposition.oneStep_fix
#print axioms OperationalDecomposition.oneStep_le_of
#print axioms OperationalDecomposition.bigStep_fix
#print axioms OperationalDecomposition.bigStep_le_of
#print axioms OperationalDecomposition.box_bigStep
