/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/

module
public import LeanTra.SRA.Howe

/-!
# Parallel reduction

Given a rule `a`, its *parallel reduction* `a⇛` relates two terms when
the second is obtained from the first by contracting any number of
`a`-redexes at once, including none. It is the standard device for
proving confluence. Single-step reduction does not have the diamond
property, since one step can duplicate a redex that the other has
already contracted; parallel reduction does have it, and its
reflexive-transitive closure is the same.

Algebraically it is the Howe extension of `Δ ⊔ a⟦Δ⟧`: the least solution
of `x = ⌃x * (Δ ⊔ a⟦Δ⟧)`. The join with `Δ` is what makes contracting
nothing an option; `a⟦Δ⟧` is the rule closed under substitution
instances, so that a redex is recognised wherever it occurs; and the
compatible refinement `⌃·` propagates the whole thing through term
structure, one layer per unfolding of the fixed point.

The file provides `parRed` and the properties of it that both routes to
confluence need: that it is compatible and reflexive, that it is substitutive
(`parRed_substitutivity`, the technical heart of the file), and the two
nesting inequalities that let a substitution be pulled apart into a
reduction followed by a base instance.

Substitutivity is where the hypothesis on the rule enters. `IsReduction a`
says the left-hand side of `a` is never a variable, `Δη * a = ⊥`. Without
it a rule could rewrite a variable, and parallel reduction would no
longer commute with substitution.

Confluence is an inequality between `(a⇛)ᵒ * a⇛` and `a⇛ * (a⇛)ᵒ`, so
every lemma about `a⇛` is needed again for `(a⇛)ᵒ`. The last section
supplies those mirrors. None of them is a new argument: each is its
forward counterpart with converse applied, using that converse is
monotone, reverses composition, and commutes with `⌃·` and with `·⟦Δ⟧`.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/



@[expose] public section
open scoped IsInvolutiveQuantale Quantale SRA
namespace LeanTra.Confluence
variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α] [SRA α]



/-! ### Reduction rules

The one hypothesis on the rule that the whole development needs. -/

/-- `a` is a reduction when its left-hand side is never a variable:
`Δη * a = ⊥`. -/
def IsReduction (a : α) : Prop := SRA.varDiag * a = ⊥



/-! ### Parallel reduction

`a⇛` and the three facts that make it usable: it contains the identity,
so contracting nothing counts as a reduction; it is compatible, so it
passes through term structure; and substituting it into the identity
stays within it. All three come from the Howe fixed-point equation, the
last two through the corresponding laws of `⌃·`. -/

/-- Parallel reduction `a⇛ := (Δ ⊔ a⟦Δ⟧)ᴴ`: any number of `a`-redexes
contracted at once, including none. -/
def parRed (a : α) : α := SRA.howe (Δ ⊔ SRA.subst a Δ)

@[inherit_doc] scoped postfix:max "⇛" => parRed

/-- `a⇛` is compatible: `⌃(a⇛) ≤ a⇛`. -/
theorem parRed_compatibility (a : α) : SRA.cr (parRed a) ≤ parRed a := by
  unfold parRed
  calc SRA.cr (SRA.howe (Δ ⊔ SRA.subst a Δ))
      = SRA.cr (SRA.howe (Δ ⊔ SRA.subst a Δ)) * Δ := (mul_one _).symm
    _ ≤ SRA.cr (SRA.howe (Δ ⊔ SRA.subst a Δ)) * (Δ ⊔ SRA.subst a Δ) :=
        mul_le_mul_right le_sup_left _
    _ = SRA.howe (Δ ⊔ SRA.subst a Δ) := (SRA.howe_fixpoint _).symm

/-- `a⇛` is reflexive: `Δ ≤ a⇛`. -/
theorem parRed_reflexivity (a : α) : (Δ : α) ≤ parRed a :=
  SRA.one_le_of_cr_le (parRed_compatibility a)

/-- Substituting `a⇛` into the identity stays within `a⇛`:
`Δ⟦a⇛⟧ ≤ a⇛`. -/
theorem parRed_leibniz (a : α) : SRA.subst Δ (parRed a) ≤ parRed a :=
  SRA.subst_one_le_of_cr_le (parRed_compatibility a)

/-- Passing to the base instance leaves parallel reduction unchanged:
`(a⟦Δ⟧)⇛ = a⇛`. -/
theorem parRed_subst_one_invariance (a : α) : parRed (SRA.subst a Δ) = parRed a := by
  unfold parRed
  rw [SRA.subst_one_idempotence]



/-! ### Substitutivity

`(a⇛)⟦a⇛⟧ ≤ a⇛`: contracting redexes and then substituting is again
contracting redexes. This is the technical heart of the file and the only
place `IsReduction` is used. The first two lemmas isolate exactly what
that hypothesis buys, namely that neither `a` nor its base instance
`a⟦Δ⟧` can act on a variable. -/

/-- A reduction factors on the left through the strict refinement of the
identity: `a = ~Δ * a`. -/
theorem scr_factorisation {a : α} (h : IsReduction a) : a = SRA.scr Δ * a := by
  have h' : SRA.varDiag * a = (⊥ : α) := h
  calc a
      = Δ * a := (one_mul _).symm
    _ = (SRA.varDiag ⊔ SRA.scr Δ) * a := by
        rw [SRA.cr_fixpoint]
    _ = SRA.varDiag * a ⊔ SRA.scr Δ * a := Quantale.sup_mul_distrib
    _ = ⊥ ⊔ SRA.scr Δ * a := by rw [h']
    _ = SRA.scr Δ * a := bot_sup_eq _

/-- The base instance of a reduction is again a reduction:
`Δη * a⟦Δ⟧ = ⊥`. -/
theorem varDiag_subst_one_orthogonality {a : α} (h : IsReduction a) : SRA.varDiag * SRA.subst a Δ = ⊥ := by
  refine le_antisymm ?_ bot_le
  have key : SRA.subst a Δ ≤ SRA.scr Δ * SRA.subst a Δ :=
    calc SRA.subst a Δ
        = SRA.subst (SRA.scr Δ * a) (Δ * Δ) := by
            rw [← scr_factorisation h, mul_one]
      _ ≤ SRA.subst (SRA.scr Δ) Δ * SRA.subst a Δ := SRA.subst_compositionality_oplax _ _ _ _
      _ ≤ SRA.scr (SRA.subst Δ Δ) * SRA.subst a Δ :=
            mul_le_mul_left (SRA.subst_scr_oplaxity _ _) _
      _ = SRA.scr Δ * SRA.subst a Δ := by rw [SRA.subst_one_one]
  calc SRA.varDiag * SRA.subst a Δ
      ≤ SRA.varDiag * (SRA.scr Δ * SRA.subst a Δ) := mul_le_mul_right key _
    _ = SRA.varDiag * SRA.scr Δ * SRA.subst a Δ := (mul_assoc _ _ _).symm
    _ ≤ ⊥ * SRA.subst a Δ :=
          mul_le_mul_left (SRA.varDiag_scr_orthogonality _) _
    _ = ⊥ := Quantale.bot_mul

/-- `a⇛` is substitutive: `(a⇛)⟦a⇛⟧ ≤ a⇛`. -/
theorem parRed_substitutivity {a : α} (h : IsReduction a) : SRA.subst (parRed a) (parRed a) ≤ parRed a := by
  refine SRA.subst_le_iff.mpr ?_
  refine SRA.howe_induction ?_
  refine SRA.subst_le_iff.mp ?_
  have hrw :
      SRA.cr (SRA.substResid (parRed a) (parRed a)) * (Δ ⊔ SRA.subst a Δ)
        = SRA.varDiag ⊔ SRA.scr (SRA.substResid (parRed a) (parRed a))
            ⊔ SRA.scr (SRA.substResid (parRed a) (parRed a)) * SRA.subst a Δ := by
    unfold SRA.cr
    rw [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
        Quantale.mul_sup_distrib, mul_one, mul_one,
        varDiag_subst_one_orthogonality h, sup_bot_eq, ← sup_assoc]
  rw [hrw, SRA.subst_join_preservation_binary_left, SRA.subst_join_preservation_binary_left]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_of_eq (SRA.subst_varDiag_unit_left _)
  · calc SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
        ≤ SRA.scr (SRA.subst (SRA.substResid (parRed a) (parRed a)) (parRed a)) :=
          SRA.subst_scr_oplaxity _ _
      _ ≤ SRA.scr (parRed a) := SRA.scr_monotonicity (SRA.subst_le_iff.mpr le_rfl)
      _ ≤ SRA.cr (parRed a) := le_sup_right
      _ ≤ parRed a := parRed_compatibility a
  · calc SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a)) * SRA.subst a Δ)
            (parRed a)
        = SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a)) * SRA.subst a Δ)
            (parRed a * Δ) := by rw [mul_one]
      _ ≤ SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
            * SRA.subst (SRA.subst a Δ) Δ :=
            SRA.subst_compositionality_oplax _ _ _ _
      _ = SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
            * SRA.subst a Δ := by
            rw [SRA.subst_associativity, SRA.subst_one_one]
      _ ≤ SRA.cr (parRed a) * SRA.subst a Δ := by
          refine mul_le_mul_left ?_ _
          calc SRA.subst (SRA.scr (SRA.substResid (parRed a) (parRed a))) (parRed a)
              ≤ SRA.scr (SRA.subst (SRA.substResid (parRed a) (parRed a)) (parRed a)) :=
                SRA.subst_scr_oplaxity _ _
            _ ≤ SRA.scr (parRed a) :=
                SRA.scr_monotonicity (SRA.subst_le_iff.mpr le_rfl)
            _ ≤ SRA.cr (parRed a) := le_sup_right
      _ ≤ SRA.cr (parRed a) * (Δ ⊔ SRA.subst a Δ) :=
          mul_le_mul_right le_sup_right _
      _ = parRed a := (SRA.howe_fixpoint _).symm



/-! ### Nesting and unfolding

Two ways of taking a composite apart. Nesting splits a substitution into
a parallel reduction followed by a base instance of the rule; unfolding
runs the fixed-point equation once, absorbing a base instance into `a⇛`.
Between them they are the reassociation both diamond arguments need. -/

/-- Nesting: `aᵒ⟦a⇛⟧ ≤ a⇛ * aᵒ⟦Δ⟧`. -/
theorem parRed_nesting (a : α) : SRA.subst aᵒ (parRed a) ≤ parRed a * SRA.subst aᵒ Δ := by
  calc SRA.subst aᵒ (parRed a)
      = SRA.subst (Δ * aᵒ) (parRed a * Δ) := by rw [one_mul, mul_one]
    _ ≤ SRA.subst Δ (parRed a) * SRA.subst aᵒ Δ := SRA.subst_compositionality_oplax _ _ _ _
    _ ≤ parRed a * SRA.subst aᵒ Δ :=
        mul_le_mul_left (parRed_leibniz a) _

/-- Unfolding: `⌃(a⇛) * a⟦Δ⟧ ≤ a⇛`. -/
theorem parRed_unfolding (a : α) : SRA.cr (parRed a) * SRA.subst a Δ ≤ parRed a :=
  calc SRA.cr (parRed a) * SRA.subst a Δ
      ≤ SRA.cr (parRed a) * (Δ ⊔ SRA.subst a Δ) :=
        mul_le_mul_right le_sup_right _
    _ = parRed a := (SRA.howe_fixpoint _).symm



/-! ### The converse side

Confluence compares `(a⇛)ᵒ * a⇛` with `a⇛ * (a⇛)ᵒ`, so every lemma above
is needed again for `(a⇛)ᵒ`. None of these is a new argument: each is its
forward counterpart with `·ᵒ` applied, using that converse is monotone,
reverses composition, and commutes with `⌃·` and with `·⟦Δ⟧`. Reading one
of the proofs is enough for all of them. -/

/-- Converse of parallel reduction: `(a⇛)ᵒ = (Δ ⊔ aᵒ⟦Δ⟧)§`. -/
theorem parRed_converse (a : α) : (parRed a)ᵒ = SRA.opHowe (Δ ⊔ SRA.subst aᵒ Δ) := by
  unfold parRed
  rw [SRA.howe_converse, IsInvolutiveQuantale.converse_join_preservation_binary,
      IsInvolutiveQuantale.converse_one, SRA.subst_converse_commutation,
      IsInvolutiveQuantale.converse_one]

/-- `(a⇛)ᵒ` is compatible: `⌃((a⇛)ᵒ) ≤ (a⇛)ᵒ`. -/
theorem parRed_converse_compatibility (a : α) : SRA.cr ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  rw [← SRA.cr_converse_commutation]
  exact IsInvolutiveQuantale.converse_monotonicity (parRed_compatibility a)

/-- Substituting `(a⇛)ᵒ` into the identity stays within `(a⇛)ᵒ`:
`Δ⟦(a⇛)ᵒ⟧ ≤ (a⇛)ᵒ`. -/
theorem parRed_converse_leibniz (a : α) : SRA.subst Δ ((parRed a)ᵒ) ≤ (parRed a)ᵒ :=
  SRA.subst_one_le_of_cr_le (parRed_converse_compatibility a)

/-- Converse of `varDiag_subst_one_orthogonality`: `aᵒ⟦Δ⟧ * Δη = ⊥`. -/
theorem subst_one_varDiag_orthogonality {a : α} (h : IsReduction a) : SRA.subst aᵒ Δ * SRA.varDiag = (⊥ : α) := by
  have hL := varDiag_subst_one_orthogonality h
  have := congrArg IsInvolutiveQuantale.converse hL
  rw [IsInvolutiveQuantale.converse_compositionality, SRA.subst_one_converse_commutation,
      SRA.varDiag_symmetry_eq, IsInvolutiveQuantale.converse_bot_strictness] at this
  exact this

/-- Converse nesting: `a⟦(a⇛)ᵒ⟧ ≤ a⟦Δ⟧ * (a⇛)ᵒ`. -/
theorem parRed_converse_nesting (a : α) : SRA.subst a ((parRed a)ᵒ) ≤ SRA.subst a Δ * (parRed a)ᵒ := by
  calc SRA.subst a ((parRed a)ᵒ)
      = SRA.subst (a * Δ) (Δ * (parRed a)ᵒ) := by rw [mul_one, one_mul]
    _ ≤ SRA.subst a Δ * SRA.subst Δ ((parRed a)ᵒ) := SRA.subst_compositionality_oplax _ _ _ _
    _ ≤ SRA.subst a Δ * (parRed a)ᵒ :=
        mul_le_mul_right (parRed_converse_leibniz a) _

/-- Converse unfolding: `aᵒ⟦Δ⟧ * ⌃((a⇛)ᵒ) ≤ (a⇛)ᵒ`. -/
theorem parRed_converse_unfolding (a : α) : SRA.subst aᵒ Δ * SRA.cr ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  have hfwd := parRed_unfolding a
  have := IsInvolutiveQuantale.converse_monotonicity hfwd
  rw [IsInvolutiveQuantale.converse_compositionality, SRA.subst_one_converse_commutation,
      SRA.cr_converse_commutation] at this
  exact this

end LeanTra.Confluence
