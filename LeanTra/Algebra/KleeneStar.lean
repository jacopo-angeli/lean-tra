/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.InvolutiveQuantale
public import Mathlib.Order.FixedPoints

/-!
# Abstract rewriting in a unital involutive quantale

The Kleene star, the diamond property, and confluence for an abstract
rewriting relation, developed inside a unital involutive quantale. This is
the quantale-level counterpart of classical abstract-reduction results
(Struth, RelMICS 2001; Struth, JLAMP 2006), and supplies the abstract half
of Gavazzo's Theorem 21 (LICS 2026) / Theorem 6 (LICS 2023).

The file is deliberately SRA-free: nothing here refers to `SRA`, `varDiag`,
substitution, or the compatible refinement. The involution is even isolated
to a second section — Section A uses only `Monoid`, `CompleteLattice`, and
`IsQuantale`. This makes the material a candidate for standalone
upstreaming to Mathlib.

## Design note — why not `KleeneAlgebra`?

Mathlib supplies `Mathlib.Algebra.Order.Kleene.KleeneAlgebra`, an idempotent
semiring with a Kleene star. Reusing it here would force `+ := ⊔`, `0 := ⊥`,
and a `Semiring` structure on `α`, creating instance-diamond risk against
the existing `CompleteLattice`. We instead define `star` directly as the
least fixed point of `x ↦ 1 ⊔ a * x` via `OrderHom.lfp`. Every Kleene-star
law we need falls out of `map_lfp` / `lfp_le`, with no algebraic refactor of
the ambient structure. If `KleeneAlgebra` grows a variant parametric over
the join semilattice/semiring identification, this file can be revisited.

## Contents

* Section A — no involution.
  * `starStep`, `star`, and its scoped postfix notation `∗`.
  * Fixed-point law `star_fix` and induction principle `star_le_of`.
  * Basic laws: `one_le_star`, `le_star`, `mul_star_le_star`, `star_mono`,
    `star_mul_star`, `star_star`, `star_one`, plus the right-handed
    `star_mul_le_star`.
  * Right-handed characterisation `star_eq_lfp_right`, needed to transport
    the fixed-point equation through the involution in Section B.
  * Sandwich lemma `star_eq_of_le_of_le` — antisymmetry via `star_mono`
    and `star_star`.
* Section B — with `IsInvolutiveQuantale`.
  * `star_converse : (star a)ᵒ = star (aᵒ)`, proved by exhibiting
    `(star a)ᵒ` as a right-fixed-point of `aᵒ` and comparing against the
    right-lfp characterisation from Section A.

## References

* Georg Struth. *Calculating Church-Rosser proofs in Kleene algebra.*
  RelMICS 2001. — The original strip / confluence argument in
  Kleene-algebra form; lemma 15 and theorem 16 here are its quantale
  transcription.
* Georg Struth. *Abstract abstract reduction.* JLAMP 2006. — Extended
  treatment; same technique.
* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Theorem 21. — Downstream consumer; the abstract confluence
  developed here is one half of that theorem.
* Francesco Gavazzo. *Allegories of Symbolic Manipulations.* LICS 2023,
  Theorem 6. — Earlier statement of the same downstream result.
-/
@[expose] public section

open scoped Quantale

namespace LeanTra.Confluence

/-! ## Section A — no involution -/

section NoInvolution

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α]
variable {a b : α}

/-- The left-handed Kleene recursor: `x ↦ 1 ⊔ a * x`, bundled as an
`OrderHom` so its least fixed point can be taken via `OrderHom.lfp`.
Internal helper for `star`. -/
def starStep (a : α) : α →o α where
  toFun x := 1 ⊔ a * x
  monotone' _ _ h := sup_le_sup_left (mul_le_mul_right h a) 1

/-- Kleene star: the least solution of `x = 1 ⊔ a * x`. Constructed as the
least fixed point via Knaster–Tarski. Every star law below is a consequence
of `map_lfp` / `lfp_le`. -/
def star (a : α) : α := (starStep a).lfp

@[inherit_doc]
scoped postfix:max "∗" => LeanTra.Confluence.star

/-- Fixed-point law: `a∗ = 1 ⊔ a * a∗`. -/
theorem star_fix (a : α) : a∗ = 1 ⊔ a * a∗ :=
  ((starStep a).map_lfp).symm

/-- Fixed-point induction: `a∗` is below every pre-fixed point of the
left-handed Kleene recursion. -/
theorem star_le_of {a x : α} (h : 1 ⊔ a * x ≤ x) : a∗ ≤ x :=
  (starStep a).lfp_le h

/-- `1 ≤ a∗`. -/
theorem one_le_star (a : α) : 1 ≤ a∗ := by
  conv_rhs => rw [star_fix]
  exact le_sup_left

/-- `a ≤ a∗`. -/
theorem le_star (a : α) : a ≤ a∗ := by
  conv_rhs => rw [star_fix]
  refine le_sup_of_le_right ?_
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * a∗ := mul_le_mul_right (one_le_star a) a

/-- `a * a∗ ≤ a∗`. -/
theorem mul_star_le_star (a : α) : a * a∗ ≤ a∗ := by
  conv_rhs => rw [star_fix]
  exact le_sup_right

/-- Monotonicity of `·∗`. -/
theorem star_mono ⦃a b : α⦄ (h : a ≤ b) : a∗ ≤ b∗ := by
  refine star_le_of ?_
  refine sup_le (one_le_star b) ?_
  calc a * b∗
      ≤ b * b∗ := mul_le_mul_left h _
    _ ≤ b∗ := mul_star_le_star b

/-- Transitivity of the star: `a∗ * a∗ ≤ a∗`. Struth's proof, transported
through the left residual `⇨ₗ`. -/
theorem star_mul_star (a : α) : a∗ * a∗ ≤ a∗ := by
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine star_le_of ?_
  refine sup_le ?_ ?_
  · exact Quantale.leftMulResiduation_le_iff_mul_le.mpr (by rw [one_mul])
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    calc a * (a∗ ⇨ₗ a∗) * a∗
        = a * ((a∗ ⇨ₗ a∗) * a∗) := mul_assoc _ _ _
      _ ≤ a * a∗ := mul_le_mul_right
          (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl) a
      _ ≤ a∗ := mul_star_le_star a

/-- Idempotence of `·∗`: `a∗∗ = a∗`. -/
theorem star_star (a : α) : a∗∗ = a∗ := by
  refine le_antisymm ?_ (le_star _)
  exact star_le_of (sup_le (one_le_star a) (star_mul_star a))

/-- `1∗ = 1`: `1` is a pre-fixed point of the Kleene recursor at `a = 1`. -/
@[simp]
theorem star_one : (1 : α)∗ = 1 := by
  refine le_antisymm ?_ (one_le_star _)
  refine star_le_of ?_
  rw [one_mul]
  exact sup_le le_rfl le_rfl

/-! ### Right-handed characterisation -/

/-- The right-handed Kleene recursor: `x ↦ 1 ⊔ x * a`, bundled as an
`OrderHom`. Needed to identify `star a` with the least fixed point of the
symmetric equation `x = 1 ⊔ x * a`; used in Section B to transport the
fixed-point identity through the involution. -/
def starStepR (a : α) : α →o α where
  toFun x := 1 ⊔ x * a
  monotone' _ _ h := sup_le_sup_left (mul_le_mul_left h a) 1

/-- Right-handed post-multiplication: `a∗ * a ≤ a∗`. Symmetric to
`mul_star_le_star`, proved via the left residual. -/
theorem star_mul_le_star (a : α) : a∗ * a ≤ a∗ := by
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  refine star_le_of ?_
  refine sup_le ?_ ?_
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    rw [one_mul]; exact le_star a
  · refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
    calc a * (a ⇨ₗ a∗) * a
        = a * ((a ⇨ₗ a∗) * a) := mul_assoc _ _ _
      _ ≤ a * a∗ := mul_le_mul_right
          (Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl) a
      _ ≤ a∗ := mul_star_le_star a

/-- Right-handed characterisation: `a∗` is also the least fixed point of
`x ↦ 1 ⊔ x * a`. Each lfp is a pre-fixed point of the other equation. -/
theorem star_eq_lfp_right (a : α) : a∗ = (starStepR a).lfp := by
  set r := (starStepR a).lfp with hr
  have r_fix : r = 1 ⊔ r * a := ((starStepR a).map_lfp).symm
  have one_le_r : (1 : α) ≤ r := by
    conv_rhs => rw [r_fix]
    exact le_sup_left
  have r_mul_le_r : r * a ≤ r := by
    conv_rhs => rw [r_fix]
    exact le_sup_right
  have a_mul_r_le_r : a * r ≤ r := by
    refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
    refine (starStepR a).lfp_le ?_
    refine sup_le ?_ ?_
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      rw [mul_one]
      calc a = 1 * a := (one_mul a).symm
        _ ≤ r * a := mul_le_mul_left one_le_r a
        _ ≤ r := r_mul_le_r
    · refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
      calc a * ((a ⇨ᵣ r) * a)
          = (a * (a ⇨ᵣ r)) * a := (mul_assoc _ _ _).symm
        _ ≤ r * a := mul_le_mul_left
            (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl) a
        _ ≤ r := r_mul_le_r
  refine le_antisymm ?_ ?_
  · exact star_le_of (sup_le one_le_r a_mul_r_le_r)
  · exact (starStepR a).lfp_le (sup_le (one_le_star a) (star_mul_le_star a))

/-- Sandwich lemma: if `a ≤ b ≤ a∗`, then `b∗ = a∗`. Antisymmetry via
`star_mono` and `star_star`. Not used by the current proof of Thm. 21;
kept as a derived law of independent interest — originally intended for
a transfer step (parallel reduction back to the ground relation) that
the final development does not perform. -/
theorem star_eq_of_le_of_le (hab : a ≤ b) (hb : b ≤ a∗) : b∗ = a∗ := by
  refine le_antisymm ?_ (star_mono hab)
  calc b∗ ≤ (a∗)∗ := star_mono hb
    _ = a∗ := star_star a

end NoInvolution

/-! ## Section B — with involution -/

section WithInvolution

open scoped IsInvolutiveQuantale

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable {a : α}

/-- Converse commutes with star: `(a∗)ᵒ = (aᵒ)∗`. Apply `·ᵒ` to `star_fix`
to exhibit `(a∗)ᵒ` as a fixed point of the *right-handed* Kleene recursor
for `aᵒ`, then compare against `star_eq_lfp_right`. The symmetric direction
comes from applying the same argument at `aᵒ` and using involutivity. -/
@[simp]
theorem star_converse (a : α) : (a∗)ᵒ = (aᵒ)∗ := by
  have h : ∀ b : α, (b∗)ᵒ = 1 ⊔ (b∗)ᵒ * bᵒ := fun b => by
    conv_lhs => rw [star_fix b]
    rw [IsInvolutiveQuantale.converse_sup, IsInvolutiveQuantale.converse_one,
        IsInvolutiveQuantale.mul_converse]
  have ge : (aᵒ)∗ ≤ (a∗)ᵒ := by
    rw [star_eq_lfp_right]
    exact (starStepR aᵒ).lfp_le (h a).ge
  have ge' : ((aᵒ)ᵒ)∗ ≤ ((aᵒ)∗)ᵒ := by
    rw [star_eq_lfp_right]
    exact (starStepR ((aᵒ)ᵒ)).lfp_le (h aᵒ).ge
  rw [IsInvolutiveQuantale.converse_involutive] at ge'
  have le : (a∗)ᵒ ≤ (aᵒ)∗ := by
    have := IsInvolutiveQuantale.converse_le_converse ge'
    simpa [IsInvolutiveQuantale.converse_involutive] using this
  exact le_antisymm le ge

end WithInvolution

end LeanTra.Confluence
