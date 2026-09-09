/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Metatheory.Confluence.ParallelReduction
public import LeanTra.Algebra.Diamond
public import LeanTra.Metatheory.GentzenPrinciples

/-!
# Confluence from local conditions on the rule

`Confluence/Orthogonal.lean` derives the diamond property of `a⇛` from
`IsOrthogonal a`. That hypothesis is adequate but not usable as a
criterion: its second conjunct mentions `a⇛` itself, so deciding whether
a given rewrite rule satisfies it presupposes knowledge of the very
object the theorem is about.

This file takes the other route. Every hypothesis is a condition on the
rule alone: `a` is a reduction, its base substitution instance `a⟦Δ⟧`
is bounded by `a`, `aᵒ * a ≤ Δ`, and the two Gentzen principles. Each
one can be read off a rewrite rule directly, and parallel reduction
occurs only in the conclusion.

The argument is organised in three layers. The bottom layer is those
four conditions on `a`. The top layer is the diamond property. Between
them sits a single intermediate condition, `IsStruct a b`, relating the
rule to an auxiliary relation `b`: it isolates exactly the amount of
interaction between rule and parallel reduction that the diamond
argument consumes, and nothing more. That is what lets the outer
hypotheses stay local: `IsStruct` is discharged at `b = (a⇛)ᵒ` from the
Gentzen principles, so it never has to be assumed.

The whole argument is the single theorem `local_confluence`, conclusion
(i) of the bridge theorem of the reference. The separators inside its
proof mark the stages: the diamond property is established from
`IsStruct`, and `IsStruct` is discharged from the Gentzen principles along
the way.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale TRA
open LeanTra.Algebra
open LeanTra.Metatheory
open OperationalDecomposition

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [OperationalDecomposition α]

/-! ### Predicates on rules

Two inequalities on the rule alone, used only in the theorem below,
alongside `IsDeterministic` from `Algebra/Diamond.lean`.
`IsSubstitutiveAtIdentity` and `IsDeterministic` are the local
counterparts of the two orthogonality conjuncts; `IsStruct` is the
intermediate condition on `(a, b)` that the diamond argument actually
consumes, and that the Gentzen principles discharge at `b = (a⇛)ᵒ`. -/

/-- `a⟦Δ⟧ ≤ a`: the base substitution instance is bounded by the rule. -/
def IsSubstitutiveAtIdentity (a : α) : Prop := TRA.subst a 1 ≤ a

/-- `~b * a ≤ a * b⟦b⟧`: a strict compatible refinement of `b` standing
in front of the rule can be pushed past it, at the cost of substituting
`b` into itself. -/
def IsStruct (a b : α) : Prop := TRA.scr b * a ≤ a * TRA.subst b b

/-! ### Confluence from local conditions

The single theorem the file exists to prove. Its five hypotheses are all
conditions on the rule; parallel reduction occurs only in the
conclusion. The proof runs in five stages, marked by the separators
inside it: rearranging the hypotheses, staging the diamond as a
post-fixed point, discharging `IsStruct a ((a⇛)ᵒ)` from the Gentzen
principles, commuting the rule past `~B`, and closing the two branches
of the inductive step. -/

theorem local_confluence {a : α}
    (h1 : IsReduction a)
    (h2 : IsSubstitutiveAtIdentity a)
    (h3 : IsDeterministic a)
    (hgip : GIP a)
    (hgcp : GCP a) :
    IsConfluent (parRed a) := by
  -- Consequences of the conditions
  --
  -- Elementary rearrangements of the hypotheses, used throughout. The first
  -- pair turns `IsSubstitutiveAtIdentity` into the equation `a[Δ] = a`, which
  -- is what allows a condition stated on the rule to be applied to the
  -- summand that actually occurs in the fixed points of `a⇛` and `(a⇛)ᵒ`.
  have hN1 : a ≤ TRA.subst a 1 := by
    calc a = TRA.subst a TRA.varDiag := (TRA.subst_varDiag_unit_right a).symm
      _ ≤ TRA.subst a 1 := TRA.subst_monotonicity_right TRA.varDiag_coreflexivity
  have hN2 : TRA.subst a 1 = a := le_antisymm h2 hN1
  have hN3 : ∀ t u : α, TRA.scr t * TRA.cr u = TRA.scr t * TRA.scr u := by
    intro t u
    unfold TRA.cr
    rw [Quantale.mul_sup_distrib,
        le_antisymm (TRA.scr_varDiag_orthogonality t) bot_le, bot_sup_eq]
  have hN4 : aᵒ * TRA.varDiag = (⊥ : α) := by
    have hL : TRA.varDiag * a = (⊥ : α) := h1
    have hc := congrArg IsInvolutiveQuantale.converse hL
    rw [IsInvolutiveQuantale.converse_compositionality, TRA.varDiag_symmetry_eq,
        IsInvolutiveQuantale.converse_bot_strictness] at hc
    exact hc
  have hN5 : ∀ {b : α}, IsStruct a b →
      aᵒ * TRA.scr (bᵒ) ≤ TRA.subst (bᵒ) (bᵒ) * aᵒ := by
    intro b h
    have hL : TRA.scr b * a ≤ a * TRA.subst b b := h
    have hc := IsInvolutiveQuantale.converse_monotonicity hL
    rw [IsInvolutiveQuantale.converse_compositionality, IsInvolutiveQuantale.converse_compositionality,
        ← TRA.scr_converse_commutation, TRA.subst_converse_commutation] at hc
    exact hc
  have hN6 : TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
    have hL := parRed_substitutivity h1
    have hc := IsInvolutiveQuantale.converse_monotonicity hL
    rw [TRA.subst_converse_commutation] at hc
    exact hc
  -- The diamond as a post-fixed point
  --
  -- Write `B` for the composite `a⇛ * (a⇛)ᵒ`, the relation the diamond
  -- property asserts to dominate `(a⇛)ᵒ * a⇛`. The proof runs by fixed-point
  -- induction on `(a⇛)ᵒ`, which is the op-Howe extension of `aᵒ ⊔ Δ`; the
  -- inductive step needs to know how `B` behaves under the compatible
  -- refinement and under composition with the rule on either side. The four
  -- facts below record that behaviour.
  have hP1 : TRA.scr (parRed a * (parRed a)ᵒ)
           = TRA.scr (parRed a) * TRA.scr ((parRed a)ᵒ) :=
    TRA.scr_compositionality _ _
  have hP2 : (parRed a * (parRed a)ᵒ)ᵒ = parRed a * (parRed a)ᵒ := by
    rw [IsInvolutiveQuantale.converse_compositionality, IsInvolutiveQuantale.converse_involutivity]
  have hP3 : TRA.scr (parRed a * (parRed a)ᵒ) ≤ parRed a * (parRed a)ᵒ := by
    rw [hP1]
    refine mul_le_mul' ?_ ?_
    · calc TRA.scr (parRed a)
          ≤ TRA.cr (parRed a) := by unfold TRA.cr; exact le_sup_right
        _ ≤ parRed a := parRed_compatibility a
    · calc TRA.scr ((parRed a)ᵒ)
          ≤ TRA.cr ((parRed a)ᵒ) := by unfold TRA.cr; exact le_sup_right
        _ ≤ (parRed a)ᵒ := parRed_converse_compatibility a
  have hP4 : (aᵒ ⊔ 1) * TRA.cr ((parRed a)ᵒ) = (parRed a)ᵒ := by
    have hnorm : ((1 : α) ⊔ TRA.subst aᵒ 1) = aᵒ ⊔ 1 := by
      rw [← TRA.subst_one_converse_commutation a, hN2]
      exact sup_comm 1 aᵒ
    rw [← hnorm]
    conv_rhs => rw [parRed_converse a, TRA.opHowe_fixpoint]
    rw [← parRed_converse a]
  -- Discharging the structural condition
  --
  -- What remains is to obtain `IsStruct a ((a⇛)ᵒ)` from the Gentzen principles,
  -- so that it need not be assumed.
  --
  -- Decompose `~b` into its constructor and destructor parts. Against the
  -- inversion principle, which factors every rule step through an elimination
  -- form, the constructor part is annihilated by intro/elim orthogonality. The
  -- destructor part is the substantial one: the conservation principle bounds
  -- `⟨~̂b, b⟩ * a`, so the major slot produced by the inversion principle must
  -- be shown to lie inside `~̂b`.
  --
  -- That last step is where the argument is specific to `b = (a⇛)ᵒ`. What is
  -- needed is that the converse of parallel reduction, composed with the
  -- coreflexive of introduction forms, stays a compatible refinement — in
  -- concrete terms, that an introduction form reduces in parallel only to an
  -- introduction form with the same outermost constructor, because it is not
  -- itself a redex. Algebraically this comes out of the op-Howe fixed point,
  -- not out of compatibility of `b`.
  have hEI : ∀ b c x : α, elimination b c * introduction x ≤ (⊥ : α) := by
    intro b c x
    rw [← IsInvolutiveQuantale.converse_monotonicity_iff,
        IsInvolutiveQuantale.converse_bot_strictness,
        IsInvolutiveQuantale.converse_compositionality,
        ← OperationalDecomposition.introduction_converse_commutation,
        ← OperationalDecomposition.elimination_converse_commutation]
    exact OperationalDecomposition.introduction_elimination_orthogonality _ _ _
  have hL2 : TRA.varDiag * (introductionCoreflexive : α) ≤ (⊥ : α) := by
    calc TRA.varDiag * (introductionCoreflexive : α)
        ≤ TRA.varDiag * TRA.scr 1 := by
          refine mul_le_mul' le_rfl ?_
          rw [OperationalDecomposition.scr_decomposition]
          exact le_sup_left
      _ ≤ ⊥ := TRA.varDiag_scr_orthogonality _
  have hL3 : ∀ x : α,
      TRA.cr x * (introductionCoreflexive : α) ≤ introduction x := by
    intro x
    have hdecomp : TRA.cr x
        = (TRA.varDiag ⊔ introduction x) ⊔ elimination x x := by
      unfold TRA.cr
      rw [OperationalDecomposition.scr_decomposition, ← sup_assoc]
    rw [hdecomp, Quantale.sup_mul_distrib, Quantale.sup_mul_distrib]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hL2.trans bot_le
    · have heq : introduction x * (introductionCoreflexive : α) = introduction x := by
        change introduction x * introduction 1 = introduction x
        rw [← OperationalDecomposition.introduction_compositionality, mul_one]
      exact heq.le
    · exact (hEI _ _ _).trans bot_le
  have hL4 : ∀ x : α, aᵒ * introduction x ≤ (⊥ : α) := by
    intro x
    have hgip_conv : aᵒ ≤ aᵒ * elimination (introduction (1 : α)) 1 := by
      have h := IsInvolutiveQuantale.converse_monotonicity hgip
      rw [IsInvolutiveQuantale.converse_compositionality,
          ← OperationalDecomposition.elimination_converse_commutation,
          ← OperationalDecomposition.introduction_converse_commutation,
          IsInvolutiveQuantale.converse_one] at h
      exact h
    calc aᵒ * introduction x
        ≤ (aᵒ * elimination (introduction 1) 1) * introduction x :=
          mul_le_mul' hgip_conv le_rfl
      _ = aᵒ * (elimination (introduction 1) 1 * introduction x) :=
          mul_assoc _ _ _
      _ ≤ aᵒ * ⊥ :=
          mul_le_mul' le_rfl (hEI _ _ _)
      _ = ⊥ := Quantale.mul_bot
  have hL5 : (parRed a)ᵒ * (introductionCoreflexive : α) ≤ TRA.cr ((parRed a)ᵒ) := by
    conv_lhs => rw [← hP4]
    rw [mul_assoc]
    calc (aᵒ ⊔ 1) * (TRA.cr ((parRed a)ᵒ) * (introductionCoreflexive : α))
        ≤ (aᵒ ⊔ 1) * introduction ((parRed a)ᵒ) :=
          mul_le_mul' le_rfl (hL3 _)
      _ = aᵒ * introduction ((parRed a)ᵒ)
            ⊔ 1 * introduction ((parRed a)ᵒ) := by
          rw [Quantale.sup_mul_distrib]
      _ = aᵒ * introduction ((parRed a)ᵒ)
            ⊔ introduction ((parRed a)ᵒ) := by rw [one_mul]
      _ ≤ TRA.cr ((parRed a)ᵒ) := by
          refine sup_le ?_ ?_
          · exact (hL4 _).trans bot_le
          · calc introduction ((parRed a)ᵒ)
                ≤ TRA.scr ((parRed a)ᵒ) := by
                  rw [OperationalDecomposition.scr_decomposition]
                  exact le_sup_left
              _ ≤ TRA.cr ((parRed a)ᵒ) := by
                  unfold TRA.cr; exact le_sup_right
  have hStruct : IsStruct a ((parRed a)ᵒ) := by
    change TRA.scr ((parRed a)ᵒ) * a
         ≤ a * TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ)
    rw [OperationalDecomposition.scr_decomposition,
        Quantale.sup_mul_distrib]
    refine sup_le ?_ ?_
    · calc introduction ((parRed a)ᵒ) * a
          ≤ introduction ((parRed a)ᵒ)
              * (elimination (introduction 1) 1 * a) := mul_le_mul' le_rfl hgip
        _ = (introduction ((parRed a)ᵒ) * elimination (introduction 1) 1) * a :=
            (mul_assoc _ _ _).symm
        _ ≤ (⊥ : α) * a :=
            mul_le_mul'
              (OperationalDecomposition.introduction_elimination_orthogonality _ _ _)
              le_rfl
        _ = (⊥ : α) := Quantale.bot_mul
        _ ≤ a * TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := bot_le
    · calc elimination ((parRed a)ᵒ) ((parRed a)ᵒ) * a
          ≤ elimination ((parRed a)ᵒ) ((parRed a)ᵒ)
              * (elimination (introduction 1) 1 * a) := mul_le_mul' le_rfl hgip
        _ = elimination ((parRed a)ᵒ) ((parRed a)ᵒ)
              * elimination (introduction 1) 1 * a :=
            (mul_assoc _ _ _).symm
        _ = elimination ((parRed a)ᵒ * introduction 1)
              ((parRed a)ᵒ * 1) * a := by
            rw [← OperationalDecomposition.elimination_compositionality]
        _ = elimination ((parRed a)ᵒ * introduction 1) ((parRed a)ᵒ) * a := by
            rw [mul_one]
        _ ≤ elimination (TRA.cr ((parRed a)ᵒ)) ((parRed a)ᵒ) * a :=
            mul_le_mul'
              (elimination_monotonicity hL5 le_rfl)
              le_rfl
        _ ≤ a * TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) :=
            hgcp _ (parRed_converse_compatibility a)
  -- Commuting the rule past `~B`
  --
  -- The three inequalities below are where the hypotheses are spent. Each says
  -- that `~B` composed with the rule — on the left, on the right, or on both
  -- sides — stays inside `B`. Determinism is consumed exactly once, in the
  -- two-sided case, to cancel the `aᵒ * a` that appears in the middle.
  have hstruct_dual : aᵒ * TRA.scr (parRed a)
                    ≤ TRA.subst (parRed a) (parRed a) * aᵒ := by
    have hd := hN5 hStruct
    rwa [IsInvolutiveQuantale.converse_involutivity] at hd
  have hL11 : aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) * a
            ≤ parRed a * (parRed a)ᵒ := by
    have hstruct : TRA.scr ((parRed a)ᵒ) * a
                 ≤ a * TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := hStruct
    calc aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) * a
        = aᵒ * (TRA.scr (parRed a) * TRA.scr ((parRed a)ᵒ)) * a := by rw [hP1]
      _ = aᵒ * TRA.scr (parRed a) * (TRA.scr ((parRed a)ᵒ) * a) := by
          simp only [mul_assoc]
      _ ≤ aᵒ * TRA.scr (parRed a) * (a * TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ)) :=
          mul_le_mul' le_rfl hstruct
      _ = aᵒ * TRA.scr (parRed a) * a * TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := by
          simp only [mul_assoc]
      _ ≤ TRA.subst (parRed a) (parRed a) * aᵒ * a *
            TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) :=
          mul_le_mul' (mul_le_mul' hstruct_dual le_rfl) le_rfl
      _ = TRA.subst (parRed a) (parRed a) * (aᵒ * a) *
            TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := by
          simp only [mul_assoc]
      _ ≤ TRA.subst (parRed a) (parRed a) * 1 *
            TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) :=
          mul_le_mul' (mul_le_mul' le_rfl h3) le_rfl
      _ = TRA.subst (parRed a) (parRed a) *
            TRA.subst ((parRed a)ᵒ) ((parRed a)ᵒ) := by rw [mul_one]
      _ ≤ parRed a * (parRed a)ᵒ :=
          mul_le_mul' (parRed_substitutivity h1) hN6
  have hL12 : aᵒ * TRA.scr (parRed a * (parRed a)ᵒ)
            ≤ parRed a * (parRed a)ᵒ := by
    calc aᵒ * TRA.scr (parRed a * (parRed a)ᵒ)
        = aᵒ * (TRA.scr (parRed a) * TRA.scr ((parRed a)ᵒ)) := by rw [hP1]
      _ = aᵒ * TRA.scr (parRed a) * TRA.scr ((parRed a)ᵒ) := by
          simp only [mul_assoc]
      _ ≤ TRA.subst (parRed a) (parRed a) * aᵒ * TRA.scr ((parRed a)ᵒ) :=
          mul_le_mul' hstruct_dual le_rfl
      _ ≤ parRed a * aᵒ * TRA.scr ((parRed a)ᵒ) :=
          mul_le_mul' (mul_le_mul' (parRed_substitutivity h1) le_rfl) le_rfl
      _ = parRed a * (aᵒ * TRA.scr ((parRed a)ᵒ)) := by simp only [mul_assoc]
      _ ≤ parRed a * ((aᵒ ⊔ 1) * TRA.cr ((parRed a)ᵒ)) := by
          refine mul_le_mul' le_rfl (mul_le_mul' le_sup_left ?_)
          unfold TRA.cr; exact le_sup_right
      _ = parRed a * (parRed a)ᵒ := by rw [hP4]
  have hL21 : TRA.scr (parRed a * (parRed a)ᵒ) * a
            ≤ parRed a * (parRed a)ᵒ := by
    have hconv := IsInvolutiveQuantale.converse_monotonicity hL12
    rw [IsInvolutiveQuantale.converse_compositionality, IsInvolutiveQuantale.converse_involutivity,
        ← TRA.scr_converse_commutation, hP2] at hconv
    exact hconv
  -- The two branches of the inductive step
  --
  -- Transposing the goal along the residuation adjunction and applying
  -- fixed-point induction to `(a⇛)ᵒ` leaves a join over `aᵒ ⊔ Δ`. The two
  -- summands are treated separately: on the first the rule annihilates the
  -- variable diagonal, on the second the diagonal survives and is absorbed by
  -- reflexivity of parallel reduction.
  set Y : α := parRed a ⇨ₗ (parRed a * (parRed a)ᵒ) with hY_def
  have counit : Y * parRed a ≤ parRed a * (parRed a)ᵒ :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hpar : parRed a = TRA.cr (parRed a) * (a ⊔ 1) := by
    have hf : parRed a = TRA.cr (parRed a) * (1 ⊔ TRA.subst a 1) := TRA.howe_fixpoint _
    rw [hN2, sup_comm 1 a] at hf
    exact hf
  have hLeaf1 : aᵒ * TRA.cr Y * parRed a ≤ parRed a * (parRed a)ᵒ := by
    calc aᵒ * TRA.cr Y * parRed a
        = aᵒ * (TRA.varDiag ⊔ TRA.scr Y) * parRed a := by rfl
      _ = (aᵒ * TRA.varDiag ⊔ aᵒ * TRA.scr Y) * parRed a := by
          rw [Quantale.mul_sup_distrib]
      _ = aᵒ * TRA.varDiag * parRed a ⊔ aᵒ * TRA.scr Y * parRed a := by
          rw [Quantale.sup_mul_distrib]
      _ = ⊥ * parRed a ⊔ aᵒ * TRA.scr Y * parRed a := by
          rw [hN4]
      _ = ⊥ ⊔ aᵒ * TRA.scr Y * parRed a := by rw [Quantale.bot_mul]
      _ = aᵒ * TRA.scr Y * parRed a := bot_sup_eq _
      _ = aᵒ * TRA.scr Y * (TRA.cr (parRed a) * (a ⊔ 1)) := by
          conv_lhs => rw [hpar]
      _ = aᵒ * (TRA.scr Y * TRA.cr (parRed a)) * (a ⊔ 1) := by
          simp only [mul_assoc]
      _ = aᵒ * (TRA.scr Y * TRA.scr (parRed a)) * (a ⊔ 1) := by rw [hN3]
      _ = aᵒ * TRA.scr (Y * parRed a) * (a ⊔ 1) := by rw [← TRA.scr_compositionality]
      _ ≤ aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) * (a ⊔ 1) :=
          mul_le_mul' (mul_le_mul' le_rfl (TRA.scr_monotonicity counit)) le_rfl
      _ = aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) * a
            ⊔ aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) * 1 := by
          rw [Quantale.mul_sup_distrib]
      _ = aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) * a
            ⊔ aᵒ * TRA.scr (parRed a * (parRed a)ᵒ) := by rw [mul_one]
      _ ≤ parRed a * (parRed a)ᵒ :=
          sup_le hL11 hL12
  have hLeaf2 : (1 : α) * TRA.cr Y * parRed a ≤ parRed a * (parRed a)ᵒ := by
    rw [one_mul]
    have h1_le_parRed_converse : (1 : α) ≤ (parRed a)ᵒ := by
      rw [← IsInvolutiveQuantale.converse_one]
      exact IsInvolutiveQuantale.converse_monotonicity (parRed_reflexivity a)
    have piece_varDiag : TRA.varDiag * parRed a ≤ parRed a * (parRed a)ᵒ := by
      calc TRA.varDiag * parRed a
          ≤ 1 * parRed a := mul_le_mul' TRA.varDiag_coreflexivity le_rfl
        _ = parRed a := one_mul _
        _ = parRed a * 1 := (mul_one _).symm
        _ ≤ parRed a * (parRed a)ᵒ := mul_le_mul' le_rfl h1_le_parRed_converse
    have piece_scr : TRA.scr Y * parRed a ≤ parRed a * (parRed a)ᵒ := by
      calc TRA.scr Y * parRed a
          = TRA.scr Y * (TRA.cr (parRed a) * (a ⊔ 1)) := by
            conv_lhs => rw [hpar]
        _ = (TRA.scr Y * TRA.cr (parRed a)) * (a ⊔ 1) := by simp only [mul_assoc]
        _ = (TRA.scr Y * TRA.scr (parRed a)) * (a ⊔ 1) := by rw [hN3]
        _ = TRA.scr (Y * parRed a) * (a ⊔ 1) := by rw [← TRA.scr_compositionality]
        _ ≤ TRA.scr (parRed a * (parRed a)ᵒ) * (a ⊔ 1) :=
            mul_le_mul' (TRA.scr_monotonicity counit) le_rfl
        _ = TRA.scr (parRed a * (parRed a)ᵒ) * a
              ⊔ TRA.scr (parRed a * (parRed a)ᵒ) * 1 := by
            rw [Quantale.mul_sup_distrib]
        _ = TRA.scr (parRed a * (parRed a)ᵒ) * a
              ⊔ TRA.scr (parRed a * (parRed a)ᵒ) := by rw [mul_one]
        _ ≤ parRed a * (parRed a)ᵒ :=
            sup_le hL21 hP3
    calc TRA.cr Y * parRed a
        = (TRA.varDiag ⊔ TRA.scr Y) * parRed a := by rfl
      _ = TRA.varDiag * parRed a ⊔ TRA.scr Y * parRed a := by
          rw [Quantale.sup_mul_distrib]
      _ ≤ parRed a * (parRed a)ᵒ := sup_le piece_varDiag piece_scr
  have hDiamond : IsDiamond (parRed a) := by
    change (parRed a)ᵒ * parRed a ≤ parRed a * (parRed a)ᵒ
    refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
    rw [parRed_converse a]
    refine TRA.opHowe_induction ?_
    rw [← parRed_converse a]
    have h2' : (TRA.subst aᵒ 1 : α) = aᵒ := by
      rw [← TRA.subst_one_converse_commutation a, hN2]
    rw [h2', sup_comm]
    refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    rw [Quantale.sup_mul_distrib, Quantale.sup_mul_distrib]
    exact sup_le hLeaf1 hLeaf2
  exact hDiamond.confluent

end LeanTra.Confluence

#print axioms LeanTra.Confluence.local_confluence
