/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Algebra.InvolutiveQuantale

/-!
# Modular involutive quantales

Experimental extension of the involutive-quantale base with the *modular
law* of allegories,

  a * b ⊓ c ≤ (a ⊓ c * bᵒ) * b.

Kept as a separate mixin over `IsInvolutiveQuantale`; nothing in the main
development depends on it.

The three coreflexive lemmas below (`coreflexive_converse`,
`coreflexive_mul_eq_inf`, `coreflexive_mul_self`) are the payload: they
give the coincidence of composition with meet on sub-`1` elements — the
allegorical fact that a plain involutive quantale cannot supply.
-/
@[expose] public section

open scoped IsInvolutiveQuantale

universe u

/-- Modular law on an involutive quantale. -/
class IsModularQuantale (α : Type u)
    [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] where
  /-- The modular law: `a * b ⊓ c ≤ (a ⊓ c * bᵒ) * b`. -/
  protected modular (a b c : α) : a * b ⊓ c ≤ (a ⊓ c * bᵒ) * b

namespace SRA

variable {α : Type u}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
variable [IsModularQuantale α]

/-- Converse of a coreflexive relation is itself. -/
theorem coreflexive_converse {R : α} (hR : R ≤ 1) : Rᵒ = R := by
  have hRo : Rᵒ ≤ (1 : α) := by
    have h := IsInvolutiveQuantale.converse_le_converse hR
    rwa [IsInvolutiveQuantale.converse_one] at h
  -- Lemma: for any S ≤ 1, S ≤ Sᵒ.
  have aux : ∀ {S : α}, S ≤ 1 → S ≤ Sᵒ := by
    intro S hS
    have hSo : Sᵒ ≤ (1 : α) := by
      have h := IsInvolutiveQuantale.converse_le_converse hS
      rwa [IsInvolutiveQuantale.converse_one] at h
    -- `S = 1 * S ⊓ 1 ≤ (1 ⊓ 1 * Sᵒ) * S = Sᵒ * S ≤ Sᵒ * 1 = Sᵒ`.
    have hmod : (1 : α) * S ⊓ 1 ≤ ((1 : α) ⊓ 1 * Sᵒ) * S :=
      IsModularQuantale.modular 1 S 1
    have hlhs : (1 : α) * S ⊓ 1 = S := by
      rw [one_mul]; exact inf_of_le_left hS
    have hrhs_inner : ((1 : α) ⊓ 1 * Sᵒ) = Sᵒ := by
      rw [one_mul]; exact inf_of_le_right hSo
    rw [hlhs, hrhs_inner] at hmod
    calc S ≤ Sᵒ * S := hmod
      _ ≤ Sᵒ * 1 := mul_le_mul' le_rfl hS
      _ = Sᵒ := mul_one _
  refine le_antisymm ?_ (aux hR)
  have := aux hRo
  rwa [IsInvolutiveQuantale.converse_involutive] at this

/-- Composition of coreflexives equals their meet. -/
theorem coreflexive_mul_eq_inf {R S : α} (hR : R ≤ 1) (hS : S ≤ 1) :
    R * S = R ⊓ S := by
  refine le_antisymm ?_ ?_
  · -- Easy half: `R * S ≤ R ⊓ S`.
    refine le_inf ?_ ?_
    · calc R * S ≤ R * 1 := mul_le_mul' le_rfl hS
        _ = R := mul_one _
    · calc R * S ≤ 1 * S := mul_le_mul' hR le_rfl
        _ = S := one_mul _
  · -- Converse: modular at (a := 1, b := S, c := R ⊓ S).
    have hSo : Sᵒ = S := coreflexive_converse hS
    have hRSle1 : R ⊓ S ≤ (1 : α) := le_trans inf_le_left hR
    have hmod : (1 : α) * S ⊓ (R ⊓ S) ≤ ((1 : α) ⊓ (R ⊓ S) * Sᵒ) * S :=
      IsModularQuantale.modular 1 S (R ⊓ S)
    have hlhs : (1 : α) * S ⊓ (R ⊓ S) = R ⊓ S := by
      rw [one_mul]
      refine inf_of_le_right ?_
      exact le_trans inf_le_right le_rfl
    -- `(R ⊓ S) * Sᵒ = (R ⊓ S) * S ≤ 1 * 1 = 1`.
    have hprod_le_one : (R ⊓ S) * S ≤ (1 : α) := by
      calc (R ⊓ S) * S ≤ 1 * 1 := mul_le_mul' hRSle1 hS
        _ = 1 := one_mul _
    have hrhs_inner : ((1 : α) ⊓ (R ⊓ S) * Sᵒ) = (R ⊓ S) * S := by
      rw [hSo]
      exact inf_of_le_right hprod_le_one
    rw [hlhs, hrhs_inner] at hmod
    -- `R ⊓ S ≤ (R ⊓ S) * S * S ≤ R * S * S ≤ R * S`.
    have hSS : S * S ≤ S := by
      calc S * S ≤ 1 * S := mul_le_mul' hS le_rfl
        _ = S := one_mul _
    calc R ⊓ S ≤ (R ⊓ S) * S * S := hmod
      _ ≤ R * S * S := mul_le_mul' (mul_le_mul' inf_le_left le_rfl) le_rfl
      _ = R * (S * S) := mul_assoc _ _ _
      _ ≤ R * S := mul_le_mul' le_rfl hSS

/-- Idempotence of a coreflexive under composition. -/
theorem coreflexive_mul_self {R : α} (hR : R ≤ 1) : R * R = R := by
  rw [coreflexive_mul_eq_inf hR hR, inf_idem]

end SRA
