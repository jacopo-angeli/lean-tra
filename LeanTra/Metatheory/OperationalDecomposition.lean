/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Derived
public import LeanTra.Metatheory.Modality

/-!
# Operational decomposition

The class `OperationalDecomposition` and its derived data: the major-slot
projection `⟨a⟩`, the value-diagonal `‾Δ` and elimination-diagonal,
the closed-values relation `Δᵥ`, and the basic monotonicity, diagonal, and
orthogonality lemmas that follow directly from the class axioms.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, intro/elim decomposition of the compatible refinement,
  value and elimination diagonals, closed-values relation, major-slot
  projection, and the transfer of the closure modality to big-step evaluation.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale

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

/-- The major-slot projection composed with the value-diagonal on the
right lands in `⊥`. -/
theorem maj_mul_introDiag_le_bot (a : α) : maj a * (introDiag : α) ≤ ⊥ := by
  change OperationalDecomposition.elim a 1
     * OperationalDecomposition.intro 1 ≤ ⊥
  exact elim_mul_intro_le_bot _ _ _

/-- The value-diagonal is below the introduction diagonal:
`Δκ = SRA.box 1 ≤ introDiag = ‾Δ`. -/
theorem valDiag_le_introDiag : (valDiag : α) ≤ introDiag := by
  change SRA.box (OperationalDecomposition.intro 1) ≤ OperationalDecomposition.intro 1
  exact SRA.box_le _

/-- The value-diagonal is sub-idempotent: `Δκ * Δκ ≤ Δκ`. -/
theorem valDiag_mul_self_le : (valDiag : α) * valDiag ≤ valDiag := by
  change SRA.box (OperationalDecomposition.intro 1) * SRA.box (OperationalDecomposition.intro 1)
      ≤ SRA.box (OperationalDecomposition.intro 1)
  refine le_trans (SRA.box_mul_box_le _ _) ?_
  rw [introDiag_mul_self]

/-- The value-diagonal is idempotent: `Δκ * Δκ = Δκ`.

**Status.** The `≤` direction is proved above via `box_mul_box_le` and
`introDiag_mul_self`. The reverse inequality `Δκ ≤ Δκ * Δκ` is expected
not to hold in an involutive quantale; it would require the modular law
which is not available here. Left as `sorry`. -/
theorem valDiag_mul_self : (valDiag : α) * valDiag = valDiag := by
  refine le_antisymm valDiag_mul_self_le ?_
  sorry

#print axioms OperationalDecomposition.valDiag_le_introDiag
#print axioms OperationalDecomposition.valDiag_mul_self_le
#print axioms OperationalDecomposition.valDiag_mul_self

