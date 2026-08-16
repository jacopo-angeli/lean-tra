/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.SRA.Basic
public import LeanTra.SRA.OperationalDecomposition

/-!
# Toy SRA model

Two-element instance of `SRA` on `Toy := Prop`, exhibited to show that the
axiom set is *consistent* — no contradiction lets the whole algebra collapse.
The carrier is genuinely two-valued (`⊥ ≠ ⊤`, `Nontrivial Toy` — both proved
below), so the axioms do not merely hold in a trivial one-element algebra.

## What this model does and does not check

The model discharges all `SRA` axioms lawfully, but with `scr := const ⊥` the
axioms governing `tilde ·` are trivial: `scr_monotonicity` is `⊥ ≤ ⊥`, `scr_compositionality` is `⊥ =
⊥ * ⊥`, `scr_converse_commutation` reduces to `rfl`, and orthogonality `varDiag * scr a ≤
⊥` holds precisely because `scr a = ⊥`. So this model *does not exercise*
the `tilde ·` axioms; it only witnesses that they do not contradict the rest.

That limitation is not an accident of the presentation — it is forced (see
next section). Any genuine test of the `tilde ·` axioms requires a carrier with
more than two elements.

## What this model actually is

The term algebra of the empty signature over one variable: a single term `x`,
`Δη = Δ`, no compound terms, so `tilde ·` and `·[·]` collapse to the trivial
values above.

## Why the data is forced on a two-element carrier

On any two-element carrier `{⊥, ⊤}` with the standard quantale structure
(`* = ∧`, `1 = ⊤`), the `SRA` data is essentially determined:

* `subst_join_preservation_left` at `s = ∅` gives `subst ⊥ b = ⊥`; but `subst varDiag b =
  b`. If `varDiag = ⊥`, then `b = ⊥` for every `b`, collapsing the algebra.
  Hence `varDiag = ⊤ = 1`.
* Then orthogonality `varDiag * scr a ≤ ⊥` becomes `scr a ≤ ⊥`, forcing
  `scr = const ⊥` — so no two-element model can test `tilde ·` non-trivially.
* Fixed-point `varDiag ⊔ scr 1 = 1` is `⊤ ⊔ ⊥ = ⊤`. ✓
* Structural induction `varDiag ⊔ scr a ≤ a → 1 ≤ a` is `⊤ ≤ a → ⊤ ≤ a`. ✓

## Data

* `a * b := a ∧ b`, `1 := True`.
* `⊥ := False`, `⊤ := True`, `⊔ := ∨`, `sSup s := ∃ p ∈ s, p` (inherited from
  Prop's complete Boolean algebra).
* `aᵒ := a` (identity converse — `*` is commutative, so contravariance is
  vacuous).
* `varDiag := True`, `scr _ := False`, `subst a b := a ∧ b`, `j := False`
  (whence the derived `box a := j * a * j = False ∧ a ∧ False = False`, as
  before).
-/
@[expose] public section

open scoped IsInvolutiveQuantale

namespace LeanTra.Structure.Model

/-- Two-element carrier: propositions themselves, viewed as a quantale under
conjunction. `def` (not `abbrev`) so that instance resolution does not unfold
`Toy` to `Prop` — the `Mul`, `Monoid`, `SRA` … instances declared below stay
attached to `Toy` and do not pollute `Prop`'s instance database. `def` is
still unfolded by definitional equality, which suffices for the propext-based
proofs. -/
def Toy : Type := Prop

namespace Toy

instance instMul : Mul Toy := ⟨And⟩
instance instOne : One Toy := ⟨True⟩

instance instMonoid : Monoid Toy where
  one_mul _ := propext ⟨And.right, fun h => ⟨trivial, h⟩⟩
  mul_one _ := propext ⟨And.left, fun h => ⟨h, trivial⟩⟩
  mul_assoc _ _ _ :=
    propext ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

instance instCompleteLattice : CompleteLattice Toy :=
  inferInstanceAs (CompleteLattice Prop)

instance instIsQuantale : IsQuantale Toy where
  mul_sSup_distrib a s := by
    change ((a ∧ sSup s : Prop)) = ⨆ b ∈ s, ((a : Prop) ∧ b)
    apply propext
    simp only [iSup_Prop_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨ha, p, hps, hp⟩; exact ⟨p, hps, ha, hp⟩
    · rintro ⟨p, hps, ha, hp⟩; exact ⟨ha, p, hps, hp⟩
  sSup_mul_distrib s a := by
    change ((sSup s ∧ (a : Prop) : Prop)) = ⨆ b ∈ s, (b ∧ (a : Prop))
    apply propext
    simp only [iSup_Prop_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨p, hps, hp⟩, ha⟩; exact ⟨p, hps, hp, ha⟩
    · rintro ⟨p, hps, hp, ha⟩; exact ⟨⟨p, hps, hp⟩, ha⟩

instance instIsInvolutiveQuantale : IsInvolutiveQuantale Toy where
  converse a := a
  converse_involutivity _ := rfl
  converse_compositionality _ _ := propext ⟨fun ⟨p, q⟩ => ⟨q, p⟩, fun ⟨p, q⟩ => ⟨q, p⟩⟩
  converse_monotonicity h := h

instance instSRA : SRA Toy where
  varDiag := True
  scr _ := False
  subst a b := a ∧ b
  varDiag_symmetry := le_refl _
  varDiag_cotransitivity := fun h => ⟨h, h⟩
  scr_monotonicity _ _ _ := le_refl _
  scr_compositionality _ _ := propext ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  scr_converse_commutation _ := rfl
  varDiag_scr_orthogonality _ := fun ⟨_, h⟩ => h
  subst_monotonicity_right _ _ _ hb := fun ⟨ha, hb'⟩ => ⟨ha, hb hb'⟩
  subst_compositionality_oplax _ _ _ _ := fun ⟨⟨ha, ha'⟩, hb, hb'⟩ => ⟨⟨ha, hb⟩, ha', hb'⟩
  subst_converse_commutation _ _ := rfl
  subst_join_preservation_left s b := by
    change ((sSup s ∧ (b : Prop) : Prop)) = sSup ((fun a : Toy => (a ∧ b : Prop)) '' s)
    rw [sSup_image]
    apply propext
    simp only [iSup_Prop_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨p, hps, hp⟩, hb'⟩; exact ⟨p, hps, hp, hb'⟩
    · rintro ⟨p, hps, hp, hb'⟩; exact ⟨⟨p, hps, hp⟩, hb'⟩
  subst_varDiag_unit_left _ := propext ⟨And.right, fun h => ⟨trivial, h⟩⟩
  subst_varDiag_unit_right _ := propext ⟨And.left, fun h => ⟨h, trivial⟩⟩
  subst_associativity _ _ _ :=
    propext ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  subst_scr_oplaxity _ _ := fun ⟨h, _⟩ => h
  cr_fixpoint :=
    propext ⟨fun _ => trivial, fun _ => Or.inl trivial⟩
  cr_induction _ h := fun _ => h (Or.inl trivial)
  j := False
  j_coreflexivity _ := trivial
  j_symmetry h := h
  j_cotransitivity h := h.elim
  j_varDiag_orthogonality := fun ⟨h, _⟩ => h.elim

/-! ## Operational-decomposition instance

Toy carries the `OperationalDecomposition` layer with
`introduction := fun _ => ⊥` and `elimination := fun _ _ => ⊥`. Every
axiom of the class becomes trivial:
- `scr = const ⊥` forces the decomposition
  `scr a = introduction a ⊔ elimination a a` to `⊥ = ⊥ ⊔ ⊥`;
- orthogonality `introduction _ * elimination _ _ ≤ ⊥` is `⊥ * ⊥ = ⊥ ≤ ⊥`;
- monotonicity, composition-, converse-, unit- and substitution-laws all
  reduce to statements about `⊥`.

**What this certifies.** Consistency of the extension — the
`OperationalDecomposition` axioms do not contradict the `SRA` layer.

**What this does NOT certify.** The introduction/elimination decomposition
is DEGENERATE here: `introductionCoreflexive = introduction 1 = ⊥`,
`eliminationCoreflexive = elimination 1 1 = ⊥`,
`valueCoreflexive = box introductionCoreflexive = ⊥`, and every recursor
definition (`evalRec`, `oneStep`, `bigStep`) collapses to `⊥`. No non-trivial
operational behaviour is exercised. A genuine test would need a
term-model instance, which we do NOT construct here (deferred to a
later phase — cf. `Instances/FirstOrder/`, which so far only provides
`SRA`, not `OperationalDecomposition`). -/
instance instOperationalDecomposition : OperationalDecomposition Toy where
  introduction _ := False
  elimination _ _ := False
  introduction_join_preservation s := by
    refine le_antisymm False.elim ?_
    refine sSup_le ?_
    rintro _ ⟨_, _, rfl⟩
    exact le_refl _
  introduction_compositionality _ _ := propext ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  introduction_converse_commutation _ := rfl
  introduction_unit_oplaxity := fun h => h.elim
  elimination_join_preservation s := by
    refine le_antisymm False.elim ?_
    refine sSup_le ?_
    rintro _ ⟨_, _, rfl⟩
    exact le_refl _
  elimination_compositionality _ _ _ _ := propext ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  elimination_converse_commutation _ _ := rfl
  elimination_unit_oplaxity := fun h => h.elim
  introduction_elimination_orthogonality _ _ _ := fun ⟨h, _⟩ => h
  scr_decomposition _ :=
    propext ⟨fun h => Or.inl h, fun h => h.elim (fun h => h) (fun h => h)⟩
  subst_introduction_oplaxity _ _ := fun ⟨h, _⟩ => h
  subst_elimination_oplaxity _ _ _ := fun ⟨h, _⟩ => h
  box_elimination_oplaxity _ _ := fun h => h.1.1

/-! ## Non-degeneracy -/

instance instNontrivial : Nontrivial Toy where
  exists_pair_ne :=
    ⟨True, False, fun h => (h.mp trivial : False)⟩

theorem bot_ne_top : (⊥ : Toy) ≠ (⊤ : Toy) := fun h =>
  (h.symm.mp trivial : False)

end Toy

end LeanTra.Structure.Model

#print axioms LeanTra.Structure.Model.Toy.instSRA
#print axioms LeanTra.Structure.Model.Toy.instOperationalDecomposition
