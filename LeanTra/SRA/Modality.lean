/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
public import Mathlib.Order.FixedPoints

/-!
# The closure modality

The modality `□a := j * a * j` and its right adjoint `♦`. Read
relationally, `j` is the identity restricted to closed terms, so `□a`
keeps exactly those pairs of `a` whose two endpoints are both closed, and
`♦a` is the largest relation whose closed part `a` already contains.

`□` is not a field of `SRA`: it is defined from the closure constant `j`,
and every law below is derived from the four `j` axioms and nothing else.
That is the point of the file. An earlier presentation took `□` as
primitive with eight axioms of its own; seven of them are the theorems
proved here, and the eighth turned out to be false — see the section on
the dropped law.

`□` is a comonad on the lattice: deflationary (`□a ≤ a`), idempotent
(`□□a = □a`) and monotone. It preserves arbitrary joins, so it has a
right adjoint, which is `♦`. On composition it is only *lax*
(`□a * □b ≤ □(a * b)`), not exact; the two absorption laws say the
composite of two closed relations is unchanged by closing either factor
again, which is the useful half in practice.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/

@[expose] public section

open scoped IsInvolutiveQuantale Quantale

namespace SRA

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [SRA α]



/-! ### Basic laws of `□`

`□` is a comonad on the lattice: deflationary, idempotent, monotone. Each
of the three is two applications of `j ≤ Δ` or one collapse of `j * j`,
and the proofs unfold the definition with `change` rather than through an
equation lemma. -/

/-- The closure modality `□a := j * a * j`: the pairs of `a` whose two
endpoints are both closed. -/
def box (a : α) : α := SRA.j * a * SRA.j
/-- `□` is deflationary: `□a ≤ a`. -/
theorem box_le (a : α) : SRA.box a ≤ a := by
  change SRA.j * a * SRA.j ≤ a
  calc SRA.j * a * SRA.j
      ≤ 1 * a * 1 := mul_le_mul' (mul_le_mul' SRA.j_coreflexivity le_rfl) SRA.j_coreflexivity
    _ = a := by rw [one_mul, mul_one]
/-- `□` is idempotent: `□(□a) = □a`. -/
theorem box_idempotence (a : α) : SRA.box (SRA.box a) = SRA.box a := by
  change SRA.j * (SRA.j * a * SRA.j) * SRA.j = SRA.j * a * SRA.j
  rw [← mul_assoc SRA.j (SRA.j * a) SRA.j] at *
  -- goal: SRA.j * (SRA.j * a) * SRA.j * SRA.j = SRA.j * a * SRA.j
  rw [← mul_assoc SRA.j SRA.j a]
  -- goal: SRA.j * SRA.j * a * SRA.j * SRA.j = SRA.j * a * SRA.j
  rw [j_idempotence, mul_assoc (SRA.j * a) SRA.j SRA.j, j_idempotence]
/-- `□` is monotone: from monotonicity of `*`. -/
theorem box_monotonicity ⦃a b : α⦄ (h : a ≤ b) : SRA.box a ≤ SRA.box b := by
  change SRA.j * a * SRA.j ≤ SRA.j * b * SRA.j
  exact mul_le_mul' (mul_le_mul' le_rfl h) le_rfl



/-! ### `□` and composition

`□` is lax over composition, not exact: `□a * □b ≤ □(a * b)`, and the
converse inequality fails — a composite of two relations can have closed
endpoints without either half passing through a closed intermediate. The
two absorption laws are the exact statements that survive: closing a
factor of an already-closed composite changes nothing.

All three collapse the middle `j * j` first; what separates them is
whether the remaining `j` is consumed by `j ≤ Δ` (the lax law) or kept
where it is (the absorption laws). -/

/-- Left absorption: `□a * □b = □(□a * b)`. -/
theorem box_absorption_left (a b : α) : SRA.box a * SRA.box b = SRA.box (SRA.box a * b) := by
  change SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
       = SRA.j * (SRA.j * a * SRA.j * b) * SRA.j
  have hL : SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc (SRA.j * a * SRA.j) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a * SRA.j) SRA.j b,
        mul_assoc (SRA.j * a) SRA.j SRA.j, j_idempotence]
  have hR : SRA.j * (SRA.j * a * SRA.j * b) * SRA.j
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc SRA.j (SRA.j * a * SRA.j) b,
        ← mul_assoc SRA.j (SRA.j * a) SRA.j,
        ← mul_assoc SRA.j SRA.j a, j_idempotence]
  rw [hL, hR]
/-- Right absorption: `□a * □b = □(a * □b)`. -/
theorem box_absorption_right (a b : α) : SRA.box a * SRA.box b = SRA.box (a * SRA.box b) := by
  change SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
       = SRA.j * (a * (SRA.j * b * SRA.j)) * SRA.j
  have hL : SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc (SRA.j * a * SRA.j) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a * SRA.j) SRA.j b,
        mul_assoc (SRA.j * a) SRA.j SRA.j, j_idempotence]
  have hR : SRA.j * (a * (SRA.j * b * SRA.j)) * SRA.j
          = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc SRA.j a (SRA.j * b * SRA.j),
        ← mul_assoc (SRA.j * a) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a) SRA.j b,
        mul_assoc (SRA.j * a * SRA.j * b) SRA.j SRA.j, j_idempotence]
  rw [hL, hR]
/-- `□` is lax over composition: `□a * □b ≤ □(a * b)`. -/
theorem box_compositionality_lax (a b : α) : SRA.box a * SRA.box b ≤ SRA.box (a * b) := by
  change SRA.j * a * SRA.j * (SRA.j * b * SRA.j) ≤ SRA.j * (a * b) * SRA.j
  have hcollapse : SRA.j * a * SRA.j * (SRA.j * b * SRA.j)
                 = SRA.j * a * SRA.j * b * SRA.j := by
    rw [← mul_assoc (SRA.j * a * SRA.j) (SRA.j * b) SRA.j,
        ← mul_assoc (SRA.j * a * SRA.j) SRA.j b,
        mul_assoc (SRA.j * a) SRA.j SRA.j, j_idempotence]
  rw [hcollapse]
  calc SRA.j * a * SRA.j * b * SRA.j
      = SRA.j * a * (SRA.j * b) * SRA.j := by
        rw [mul_assoc (SRA.j * a) SRA.j b]
    _ ≤ SRA.j * a * (1 * b) * SRA.j :=
        mul_le_mul' (mul_le_mul' le_rfl
          (mul_le_mul' SRA.j_coreflexivity le_rfl)) le_rfl
    _ = SRA.j * a * b * SRA.j := by rw [one_mul]
    _ = SRA.j * (a * b) * SRA.j := by rw [mul_assoc SRA.j a b]



/-! ### `□` and the rest of the structure

Converse passes through `□` on the nose, because `j` is self-converse and
conjugation by it is symmetric. Joins pass through on the nose too, from
the two quantale distributivity laws — which is what makes `♦` exist.
Variables do not pass through at all: no variable is closed, so `□Δη`
collapses to `⊥`. -/

/-- `□` commutes with converse: `(□a)ᵒ = □(aᵒ)`. -/
theorem box_converse_commutation (a : α) : (SRA.box a)ᵒ = SRA.box (aᵒ) := by
  change (SRA.j * a * SRA.j)ᵒ = SRA.j * aᵒ * SRA.j
  calc (SRA.j * a * SRA.j)ᵒ
      = (SRA.j)ᵒ * (SRA.j * a)ᵒ := IsInvolutiveQuantale.converse_compositionality _ _
    _ = (SRA.j)ᵒ * (aᵒ * (SRA.j)ᵒ) := by rw [IsInvolutiveQuantale.converse_compositionality]
    _ = SRA.j * (aᵒ * SRA.j) := by rw [j_symmetry_eq]
    _ = SRA.j * aᵒ * SRA.j := (mul_assoc _ _ _).symm
/-- `□` preserves arbitrary joins. -/
theorem box_join_preservation (s : Set α) : SRA.box (sSup s) = sSup (SRA.box '' s) := by
  refine le_antisymm ?_ ?_
  · rw [show SRA.box (sSup s) = SRA.j * sSup s * SRA.j from rfl,
      mul_assoc, sSup_mul_distrib, ← sSup_image,
      mul_sSup_distrib, ← sSup_image, Set.image_image]
    refine sSup_le_sSup ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    change SRA.box y = SRA.j * (y * SRA.j)
    rw [box, mul_assoc]
  · refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact box_monotonicity (le_sSup hy)
/-- `□` preserves binary joins: `□(a ⊔ b) = □a ⊔ □b`. -/
theorem box_join_preservation_binary (a b : α) : SRA.box (a ⊔ b) = SRA.box a ⊔ SRA.box b := by
  have h := box_join_preservation ({a, b} : Set α)
  rwa [sSup_pair, Set.image_pair, sSup_pair] at h
/-- `□` and `Δη` are orthogonal: `□Δη = ⊥`. -/
theorem box_varDiag_orthogonality : SRA.box (SRA.varDiag : α) = ⊥ := by
  change SRA.j * SRA.varDiag * SRA.j = ⊥
  refine le_antisymm ?_ bot_le
  calc SRA.j * SRA.varDiag * SRA.j
      ≤ (⊥ : α) * SRA.j := mul_le_mul' SRA.j_varDiag_orthogonality le_rfl
    _ = ⊥ := Quantale.bot_mul



/-! ### The law that does not hold: `(□a)⟦b⟧ ≤ □a`

Substituting into a closed relation does not keep it closed. This was the
eighth axiom of the primitive-`□` presentation, and it is the one that
does not survive the passage to `□ := j * · * j`.

It does not derive. Every route through the oplax
`subst_compositionality_oplax` leaks the middle factor into a term
`a⟦c⟧` with `c ∈ {Δ, b}`, and nothing bounds `a⟦c⟧` above by `a` — only
below, via `subst_varDiag_unit_right` and `Δη ≤ Δ`. The bound one
actually obtains is `□(a⟦b⟧)`, which is incomparable with `□a`.

It is also false. In the context-indexed term model of
`Instances/FirstOrder`, with `j` the identity on closed terms, take
`a` to be the relation holding at every non-empty context and `b := ⊤`.
At the empty context the left-hand side holds by instantiating the outer
existential at a non-empty context, while the right-hand side reduces to
`Nonempty Empty`. So the law is dropped rather than re-axiomatised. -/



/-! ### The diamond `♦`

`♦a := sSup {x | □x ≤ a}`, the largest relation whose closed part `a`
contains. Since `□` preserves arbitrary joins, that supremum is itself a
candidate and the adjunction `□ ⊣ ♦` follows. -/

/-- The diamond `♦a := sSup {x | □x ≤ a}`: the largest relation whose
closed part `a` contains. -/
def dia (a : α) : α := sSup {x | SRA.box x ≤ a}
/-- `♦` is monotone. -/
theorem dia_monotonicity ⦃a a' : α⦄ (h : a ≤ a') : dia a ≤ dia a' :=
  sSup_le_sSup fun _ hx => le_trans hx h
/-- Introduction half of the adjunction: `□a ≤ b` gives `a ≤ ♦b`. -/
theorem le_dia_of_box_le {a b : α} (h : SRA.box a ≤ b) : a ≤ dia b :=
  le_sSup h
/-- The adjunction `□ ⊣ ♦`: `□a ≤ b ↔ a ≤ ♦b`. -/
theorem box_le_iff {a b : α} : SRA.box a ≤ b ↔ a ≤ dia b := by
  refine ⟨le_dia_of_box_le, fun h => ?_⟩
  calc SRA.box a
      ≤ SRA.box (dia b) := box_monotonicity h
    _ = sSup (SRA.box '' {x | SRA.box x ≤ b}) := box_join_preservation _
    _ ≤ b := by
        refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hx



/-! ### Closed relations

A relation is closed when it is its own `□` or equivalently, when both
endpoints of every pair it relates are closed. The inequality
`a ≤ □a` suffices as a definition, since `box_le` gives the other half. -/

/-- `a` is closed when it refines its own `□`. -/
def IsClosed (a : α) : Prop := a ≤ SRA.box a
/-- `a` is closed iff `□a = a`. -/
theorem isClosed_iff {a : α} : IsClosed a ↔ SRA.box a = a :=
  ⟨fun h => le_antisymm (box_le a) h, fun h => h.ge⟩
/-- `□a` is closed. -/
theorem box_isClosed (a : α) : IsClosed (SRA.box a) := (box_idempotence a).ge
/-- `⊥` is closed. -/
theorem isClosed_bot : IsClosed (⊥ : α) := bot_le



/-! ### Closed functions and the fixed-point transfer

A monotone `F` is *closed* when `□ ∘ F ≤ F ∘ □` pointwise: applying `F`
never opens up what was closed. For such an `F`, closing commutes with
taking the least fixed point, `□(μF) = μ(□ ∘ F)`. This is what would let
a relation defined by recursion on open terms be restricted to closed
ones without redoing the recursion. -/

/-- `F` is closed when `□ ∘ F ≤ F ∘ □` pointwise. -/
def IsClosedFun (F : α →o α) : Prop := ∀ x, SRA.box (F x) ≤ F (SRA.box x)
/-- `□ ∘ F`, bundled as an `OrderHom`. -/
def boxComp (F : α →o α) : α →o α where
  toFun x := SRA.box (F x)
  monotone' _ _ h := box_monotonicity (F.mono h)
/-- Transfer lemma: for a closed monotone `F`, `□(μF) = μ(□∘F)`. -/
theorem box_lfp {F : α →o α} (hF : IsClosedFun F) :
    SRA.box F.lfp = (boxComp F).lfp := by
  refine le_antisymm ?_ ?_
  · refine box_le_iff.mpr ?_
    refine F.lfp_le ?_
    refine box_le_iff.mp ?_
    calc SRA.box (F (dia (boxComp F).lfp))
        = SRA.box (SRA.box (F (dia (boxComp F).lfp))) := (box_idempotence _).symm
      _ ≤ SRA.box (F (SRA.box (dia (boxComp F).lfp))) := box_monotonicity (hF _)
      _ ≤ SRA.box (F (boxComp F).lfp) :=
          box_monotonicity (F.mono (box_le_iff.mpr le_rfl))
      _ = (boxComp F).lfp := (boxComp F).map_lfp
  · refine (boxComp F).lfp_le ?_
    change SRA.box (F (SRA.box F.lfp)) ≤ SRA.box F.lfp
    calc SRA.box (F (SRA.box F.lfp))
        ≤ SRA.box (F F.lfp) := box_monotonicity (F.mono (box_le _))
      _ = SRA.box F.lfp := by rw [F.map_lfp]



/-! ### Open questions

Two statements about `□` that are neither proved nor part of the class.

`SubstJClosed` below asserts that substituting by `j` yields a closed
relation. It holds in the term model
(`Instances.FirstOrder.SynRel.substJClosed`) but is not derivable from
the axioms, and nothing consumes it yet; it is recorded as a candidate
rather than assumed.

The exact multiplicativity `□(a * b) ≤ □a * □b` is *refuted* in the term
model, by `Instances.FirstOrder.SynRel.not_box_mul_le_mul_box`. Only the
lax half above survives under `□ := j * · * j`. This is expected to block
a direct application of `box_lfp` to an evaluation recursor, which is why
the evaluation development does not use it. -/

/-- Candidate axiom: substituting by `j` yields a closed relation. -/
def SubstJClosed (α : Type*) [Monoid α] [CompleteLattice α]
    [IsQuantale α] [IsInvolutiveQuantale α] [SRA α] : Prop :=
  ∀ a : α, SRA.IsClosed (SRA.subst a SRA.j)



/-! ### Notation -/

@[inherit_doc] scoped prefix:max "□" => SRA.box
@[inherit_doc] scoped prefix:max "♦" => SRA.dia

end SRA


#print axioms SRA.box_le_iff
#print axioms SRA.box_lfp
