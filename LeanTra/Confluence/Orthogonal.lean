/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Structure.Derived
public import LeanTra.Confluence.Abstract
public import Mathlib.Order.FixedPoints

/-!
# Confluence of orthogonal reduction

Gavazzo's confluence-of-orthogonal-reduction theorem (LICS 2023
"Allegories of Symbolic Manipulations" Theorem 6; LICS 2026 Theorem 21)
on top of the abstract rewriting infrastructure in
`Confluence/Abstract.lean`.

## Contents

* Reflexive substitution closure and orthogonality:
  * `IsReduction a := Δη * a = ⊥` — the LHS of a rule is never a
    variable (Gavazzo LICS'23 Remark 5 / LICS'26 Def. 17).
  * `parRed a := (1 ⊔ a[1])ᴴ` — parallel reduction as the Howe
    extension of the reflexive substitution closure of `a`.
  * `IsOrthogonal a` — the two orthogonality conjuncts (identity on
    variables, plus a strict-refinement swap) of Gavazzo LICS'23
    Theorem 6, with the paper's `SF` replaced by our `parRed`. Def. 12
    is the original statement, for `a^SP` (parallel reduction); Thm. 6
    is the restatement for `a^SF` that we transcribe.
* Elementary properties of `parRed`:
  * `cr_parRed_le` (compatibility of parallel reduction) and
    `subst_one_parRed_le` (Leibniz at `parRed`) — used throughout the
    diamond argument.
  * `one_le_parRed` (structural induction lifted) and
    `parRed_arg_le_parRed` (`1 ⊔ a[1] ≤ a⇛`) — unused by the current
    proof of Thm. 21, kept for independent interest.
* SRA S-lemmas (draft appendix labels in parentheses):
  * `SRA.subst_one_one` — S24, `1[1] = 1`.
  * `subst_one_sup_subst_one_absorbs` — corollary of S24 giving the
    hypothesis H15 the substitutivity pass needs: the reflexive
    substitution closure is closed under `·[1]`.
  * `SRA.cr_subst_le` — S27, `(aˆ)[b] ≤ b ⊔ (a[b])ˆ`.
  * `SRA.subst_one_le_of_cr_le` — S36, compatibility implies Leibniz:
    if `aˆ ≤ a` then `1[a] ≤ a`.
* **H15 — substitutivity of parallel reduction, for reductions:**
  `parRed_subst_le (h : IsReduction a) : a⇛[a⇛] ≤ a⇛`. Independent of
  the diamond argument (`diamond_parRed` routes through `nesting`),
  kept as a result in its own right — this is Gavazzo LICS'23 Prop. 10.
  The reduction hypothesis is essential — a preliminary attempt without
  it ran into two independent circularities in the Howe induction step:
  the right factor `r[r]` collapses to `a[rᴴ] ≤ rᴴ`, which unfolds to
  the main goal, and closing the product needs transitivity
  `rᴴ * rᴴ ≤ rᴴ`, which reduces to the same substitutivity question one
  level up.
  Gavazzo LICS'23 Rem. 5 / LICS'26 Def. 17 both assume `Δη * a = ⊥`
  precisely so this circularity does not arise. The hypothesis enters
  via `factor_scr_of_isReduction` (`a = ẽ 1 * a`) and its lifted form
  `varDiag_mul_subst_one_eq_bot` (`Δη * a[1] = ⊥`), which is what
  lets the `Δη * a[1]` summand of the Howe induction step vanish.
* **Converse of parRed** (`parRed_converse`) and **nesting**
  (`nesting`, Gavazzo LICS'23 Lemma 3): general-purpose computations
  feeding the diamond argument. `parRed_converse` rewrites
  `(a⇛)ᵒ` into the op-Howe form; `nesting` proves `aᵒ[a⇛] ≤ a⇛ * aᵒ[1]`
  directly (without going through `parRed_subst_le`, as the paper
  does — the paper's detour is a uniformity choice, not a necessity).
* **Diamond and Confluence.** `diamond_parRed
  (h : IsReduction a) (horth : IsOrthogonal a) : Diamond (parRed a)`
  and its corollary `confluent_parRed`, transporting confluence up
  through the Kleene star via `Diamond.confluent` from
  `Confluence/Abstract.lean`.

  The key move against a preliminary attempt was **inducting on the
  LEFT factor** — `opHowe_le_of_mul_cr_le` on `(a⇛)ᵒ` after
  `parRed_converse`, not `howe_le_of_cr_mul_le` on `a⇛` — which
  swaps the trailing `a[1]` from being next to the opaque residual
  (where the determinism conjunct `horth.1` could never fire) to
  being sandwiched by the two endpoints. The middle collapses by
  `cr_mul` and the residual defn, and the sup expansion produces a
  2×2 case matrix over the endpoints `(1, aᵒ[1]) × (1, a[1])`: this
  is the algebraic form of the classical parallel-moves case
  analysis. Corners closed by:
   * `(1, 1)`: `cr_parRed_le` and its converse `cr_parRed_converse_le`.
   * `(1, a[1])`: `varDiag_mul_subst_one_eq_bot` (L1) kills the
     `Δη`-branch; `scr_parRed_converse_mul_le` (M7) and
     `co_nesting` (M5) close the `ẽ`-branch.
   * `(aᵒ[1], 1)`: `subst_one_mul_varDiag_eq_bot` (M2, the converse
     of L1) kills the `Δη`-branch; `horth.2` and `nesting` close the
     `ẽ`-branch, with the last step through
     `subst_one_mul_cr_parRed_converse_le` (M8, the converse of M6).
   * `(aᵒ[1], a[1])` — **the critical corner**, closed by chaining
     `horth.2 + nesting + M7 + M5 + horth.1`. This is the corner
     where the determinism conjunct `horth.1` fires.

  Scope note: LICS'23 Thm. 6 / LICS'26 Thm. 21 as stated by the
  papers are `Diamond (parRed a)` / `Confluent (parRed a)`, which
  is what is proved here. The paper's stated *payoff* is then the
  Church–Rosser property of `a⇛` and, through it, consistency of
  convertibility via `a≈ = (a⇛ ∨ a⇛ᵒ)∗` (LICS'26 §4). Neither
  Church–Rosser nor that identity is formalised here — LICS'26 calls
  both "standard algebraic calculations"; the Church–Rosser TODO
  already sits in `Confluence/Abstract.lean`. Transfer to a
  *sequential* one-step relation — collapsing the `∗` of `parRed`
  to the `∗` of `a` via the linear compatible refinement (LICS'23
  §IX) — is a separate matter and remains future work of the author,
  outside the current SRA vocabulary.
* Op-Howe mirror. The design note in `Derived.lean` announced this;
  we develop only what the diamond argument needs:
  * `SRA.opHoweStep`, `SRA.opHowe` — the least solution of
    `x = a * cr x` (multiplication now on the *left*, mirror of
    `howe`).
  * Fixed-point law `SRA.opHowe_fix`, induction principle
    `SRA.opHowe_le_of_mul_cr_le`, uniqueness `SRA.opHowe_unique` /
    `SRA.opHowe_eq_of_fix` (residual argument via `⇨ᵣ`, mirror of
    `howe_solution_le`).
  * `SRA.howe_converse : (aᴴ)ᵒ = (aᵒ)§` — the announced left/right
    swap of Howe under converse.
* Scoped postfix `§` for `SRA.opHowe`.

## Development history

The file was built in three passes: (1) definitions, S-lemmas and the
op-Howe mirror; (2) substitutivity of `parRed` (H15); (3) nesting, the
diamond property, and the final confluence theorem via
`Diamond.confluent` from `Confluence/Abstract.lean`. The circularity
diagnosis recorded under H15 and the induction-side diagnosis recorded
under `diamond_parRed` in the Contents block come from the failed first
attempts at passes 2 and 3 respectively; both are kept as prose because
they explain *why* the hypotheses and the induction side are what they
are.

## References

* Francesco Gavazzo. *Allegories of Symbolic Manipulations.*
  LICS 2023, Theorem 6. — The original statement of confluence for
  orthogonal reduction in the allegory setting; Def. 12 gives the
  orthogonality conditions transcribed as `IsOrthogonal` here.
* Francesco Gavazzo. *An Algebraic Approach to Formal System
  Metatheory.* LICS 2026, Theorem 21 and Def. 17 (`IsReduction`),
  Def. 15's LICS'26 revision (`parRed := (Δ ∨ a[Δ])ᴴ`, moving
  reflexivity into the argument rather than the recursor).
* Author's draft appendix of derived SRA laws. S24, S27, S36 are the
  labels used there.
-/
@[expose] public section

open scoped IsInvolutiveQuantale Quantale SRA LeanTra.Confluence

namespace SRA

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-! ### S-lemmas -/

/-- **S24.** `1[1] = 1`: substituting the identity into the identity is the
identity. The `≥` direction is direct — `Δη ≤ 1` and `subst` is monotone in
the first argument, so `1 = Δη[1] ≤ 1[1]`. The `≤` direction moves the goal
through the substitution/residual adjunction (`subst_le_iff`) to `1 ≤ 1 » 1`,
which follows by structural induction (`one_le_of_cr_le`) — the pre-fixed-
point obligation `(1 » 1)ˆ ≤ 1 » 1` unpacks via `subst_sup_left`,
`subst_varDiag_left`, `subst_scr_le`, and `scr_one_le`. -/
theorem subst_one_one : SRA.subst (1 : α) 1 = 1 := by
  refine le_antisymm ?_ ?_
  · refine subst_le_iff.mpr ?_
    refine one_le_of_cr_le ?_
    refine sup_le ?_ ?_
    · exact subst_le_iff.mp (by rw [SRA.subst_varDiag_left])
    · refine subst_le_iff.mp ?_
      calc SRA.subst (SRA.scr ((1 : α) » 1)) 1
          ≤ SRA.scr (SRA.subst ((1 : α) » 1) 1) := SRA.subst_scr_le _ _
        _ ≤ SRA.scr 1 := SRA.scr_mono (subst_le_iff.mpr le_rfl)
        _ ≤ 1 := scr_one_le
  · calc (1 : α)
        = SRA.subst SRA.varDiag 1 := (SRA.subst_varDiag_left 1).symm
      _ ≤ SRA.subst 1 1 := subst_mono_left varDiag_le_one

/-- **Corollary of S24.** The reflexive substitution closure of `a` is
closed under `·[1]`: applying substitution again to `1 ⊔ a[1]` yields
nothing new. Proved as an *equality* under the hood (`≤` is what the
substitutivity pass — Gavazzo's H15 — actually consumes). Uses S24
(`subst_one_one`), `subst_sup_left`, and `subst_assoc`.

Not used by the current proof of Thm. 21; kept as a derived law of
independent interest. -/
theorem subst_one_sup_subst_one_absorbs (a : α) :
    SRA.subst ((1 : α) ⊔ SRA.subst a 1) 1 ≤ 1 ⊔ SRA.subst a 1 := by
  refine le_of_eq ?_
  calc SRA.subst ((1 : α) ⊔ SRA.subst a 1) 1
      = SRA.subst 1 1 ⊔ SRA.subst (SRA.subst a 1) 1 := subst_sup_left _ _ _
    _ = 1 ⊔ SRA.subst a 1 := by
        rw [subst_one_one, SRA.subst_assoc, subst_one_one]

/-- **S27.** `(aˆ)[b] ≤ b ⊔ (a[b])ˆ`: substituting into a compatible
refinement is bounded by either "hitting a variable and returning `b`" or
"refining the substitution". Direct calculation: unfold `ˆ`, apply
`subst_sup_left`, then `subst_varDiag_left` on the `Δη` summand (giving the
extra `b`) and `subst_scr_le` on the `ẽ·` summand. -/
theorem cr_subst_le (a b : α) :
    SRA.subst (SRA.cr a) b ≤ b ⊔ SRA.cr (SRA.subst a b) := by
  unfold SRA.cr
  rw [subst_sup_left, SRA.subst_varDiag_left]
  exact sup_le_sup_left ((SRA.subst_scr_le _ _).trans le_sup_right) b

/-- **S36 (compatibility implies Leibniz).** If `a` is closed under
compatible refinement (`aˆ ≤ a`), then it is also closed under
substituting the identity: `1[a] ≤ a`. Move the goal to
`1 ≤ a » a` via the adjunction; the pre-fixed-point obligation `(a » a)ˆ ≤
a » a` collapses through `cr_subst_le` (S27) and the hypothesis. -/
theorem subst_one_le_of_cr_le {a : α} (h : SRA.cr a ≤ a) :
    SRA.subst 1 a ≤ a := by
  refine subst_le_iff.mpr ?_
  refine one_le_of_cr_le ?_
  refine subst_le_iff.mp ?_
  calc SRA.subst (SRA.cr (a » a)) a
      ≤ a ⊔ SRA.cr (SRA.subst (a » a) a) := cr_subst_le _ _
    _ ≤ a ⊔ SRA.cr a := sup_le_sup_left (cr_mono (subst_le_iff.mpr le_rfl)) a
    _ ≤ a ⊔ a := sup_le_sup_left h a
    _ = a := sup_idem a

/-! ### Op-Howe extension `·§` -/

/-- Op-Howe recursor: `x ↦ a * cr x`, bundled as an `OrderHom` so its
least fixed point can be taken via `OrderHom.lfp`. Mirror of `howeStep` with
the multiplication moved to the left; internal helper for `opHowe`. -/
def opHoweStep (a : α) : α →o α where
  toFun x := a * SRA.cr x
  monotone' _ _ h := mul_le_mul_right (cr_mono h) a

/-- Op-Howe extension `·§`: the unique solution of `x = a * cr x` (see
`opHowe_unique`). Mirror of `howe`, needed because the *converse* of the
Howe equation `x = cr x * a` — obtained by applying `·ᵒ` — puts the
multiplication on the opposite side; see `howe_converse`. -/
def opHowe (a : α) : α := (opHoweStep a).lfp

/-- Fixed-point law: `a§` satisfies `a§ = a * cr a§`. Mirror of
`howe_fix`. -/
theorem opHowe_fix (a : α) : opHowe a = a * SRA.cr (opHowe a) :=
  ((opHoweStep a).map_lfp).symm

/-- Fixed-point induction: `a§` is below every pre-fixed point of the
op-Howe recursion. Mirror of `howe_le_of_cr_mul_le`. -/
theorem opHowe_le_of_mul_cr_le ⦃a x : α⦄ (h : a * SRA.cr x ≤ x) :
    opHowe a ≤ x := (opHoweStep a).lfp_le h

/-- One direction of uniqueness for the op-Howe equation: any two solutions
of `x = a * cr x` are mutually below each other. Mirror of
`howe_solution_le`, with the right residual `⇨ᵣ` in place of the left
residual `⇨ₗ` — the multiplication is on the left, so it is the *right*
residual that adjoints the induction. -/
private theorem opHowe_solution_le {a b c : α}
    (hb : b = a * SRA.cr b) (hc : c = a * SRA.cr c) : b ≤ c := by
  rw [show b = b * 1 from (mul_one b).symm]
  refine Quantale.rightMulResiduation_le_iff_mul_le.mp ?_
  refine one_le_of_cr_le ?_
  refine Quantale.rightMulResiduation_le_iff_mul_le.mpr ?_
  calc b * SRA.cr (b ⇨ᵣ c)
      = (a * SRA.cr b) * SRA.cr (b ⇨ᵣ c) := by rw [← hb]
    _ = a * (SRA.cr b * SRA.cr (b ⇨ᵣ c)) := mul_assoc _ _ _
    _ = a * SRA.cr (b * (b ⇨ᵣ c)) := by rw [cr_mul]
    _ ≤ a * SRA.cr c := mul_le_mul_right
        (cr_mono (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl)) _
    _ = c := hc.symm

/-- Uniqueness: `x = a * cr x` has at most one solution — so `a§` is not
merely the *least* solution, it is the *only* solution. Mirror of
`howe_unique`. -/
theorem opHowe_unique {a b c : α} (hb : b = a * SRA.cr b)
    (hc : c = a * SRA.cr c) : b = c :=
  le_antisymm (opHowe_solution_le hb hc) (opHowe_solution_le hc hb)

/-- Usable form of uniqueness: anything satisfying the op-Howe equation
*is* the op-Howe extension. Lets an alternative construction be identified
with `opHowe`. Mirror of `howe_eq_of_fix`. -/
theorem opHowe_eq_of_fix {a b : α} (hb : b = a * SRA.cr b) : b = opHowe a :=
  opHowe_unique hb (opHowe_fix a)

/-- Converse of Howe is op-Howe of converse: `(aᴴ)ᵒ = (aᵒ)§`. Take `·ᵒ` of
`howe_fix a` to exhibit `(aᴴ)ᵒ` as a solution of the op-Howe equation for
`aᵒ` (using `mul_converse` to swap the factors and `cr_converse` to move
`·ᵒ` under `ˆ`), then conclude by `opHowe_eq_of_fix`. Same architecture as
`star_converse` in `Confluence/Abstract.lean` — never proved directly
against the lfp; always routed through uniqueness. -/
theorem howe_converse (a : α) : (SRA.howe a)ᵒ = opHowe (aᵒ) := by
  refine opHowe_eq_of_fix ?_
  calc (SRA.howe a)ᵒ
      = (SRA.cr (SRA.howe a) * a)ᵒ := by rw [← howe_fix]
    _ = aᵒ * (SRA.cr (SRA.howe a))ᵒ := IsInvolutiveQuantale.mul_converse _ _
    _ = aᵒ * SRA.cr ((SRA.howe a)ᵒ) := by rw [cr_converse]

end SRA

/-! ## Notation

Scoped postfix `§` for the op-Howe extension. Symbolic conventions follow
the paper: `·ᴴ` for the standard Howe recursor `x ↦ cr x * a`, `·§` for
its mirror `x ↦ a * cr x`. -/

@[inherit_doc SRA.opHowe]
-- Precedence pitfall (same as `ˆ`, `ᴴ`): `ẽa§` parses as `ẽ(a§)` since
-- postfix `§` (max) binds before prefix `ẽ` (also max). For the reading
-- `(ẽa)§`, always write the explicit parens.
scoped[SRA] postfix:max "§" => SRA.opHowe

/-! ## Confluence definitions -/

namespace LeanTra.Confluence

variable {α : Type*}
variable [Monoid α] [CompleteLattice α] [IsQuantale α] [IsInvolutiveQuantale α]
  [SRA α]

/-- `a` is a *reduction* when its LHS is never a variable: `Δη * a = ⊥`.
Gavazzo LICS'23 Remark 5 / LICS'26 Def. 17. -/
def IsReduction (a : α) : Prop := SRA.varDiag * a = ⊥

/-- Parallel reduction `a⇛`: the Howe extension of the *reflexive
substitution closure* `1 ⊔ a[1]` of `a`. Note that `1` here is the
monoid unit (the paper's `Δ`, the full identity), not `Δη` (the
variable-restricted identity).

**Definitional alignment.** LICS'23 Def. 15 folds reflexivity *into the
recursor* — parallel reduction there is the least fixed point of
`x = Δ ∨ cr x * a` — and Definition 15's footnote gives the plain
`x = cr x * a` variant, which is our `howe`. LICS'26 instead moves
reflexivity into the *argument* of the plain recursor:
`a⇛ := (Δ ∨ a[Δ])ᴴ`. We follow LICS'26; both presentations agree once
`Δη ⊔ ẽ 1 = 1` (an SRA axiom) is used to align the base cases. -/
def parRed (a : α) : α := SRA.howe (1 ⊔ SRA.subst a 1)

/-! ### Elementary properties of `parRed`

Four laws about `parRed`: compatibility (`cr_parRed_le`), Leibniz at
`parRed` (`subst_one_parRed_le`), the structural containment `1 ≤ a⇛`
(`one_le_parRed`), and the reflexive-substitution-closure containment
`1 ⊔ a[1] ≤ a⇛` (`parRed_arg_le_parRed`). The first two feed both the
substitutivity pass (H15, LICS'23 Prop. 10) and the diamond argument
downstream; the last two are unused by the current proof of Thm. 21
and are kept for independent interest. -/

/-- Trivial base of the reflexive-substitution-closure argument used in
`parRed`: `1 ≤ 1 ⊔ a[1]`. Not deep — one `le_sup_left`. Split out as a
named lemma to keep the calculations below in a uniform style
(`mul_le_mul_*` prefers a named hypothesis). -/
theorem one_le_parRed_arg (a : α) : (1 : α) ≤ 1 ⊔ SRA.subst a 1 :=
  le_sup_left

/-- **Compatibility of parallel reduction.** `(a⇛)ˆ ≤ a⇛`: refining
`parRed a` structurally does not escape it. Direct calculation:
`cr (howe r) = cr (howe r) * 1 ≤ cr (howe r) * (1 ⊔ a[1]) = howe r` by
`mul_one`, `mul_le_mul_right` with `one_le_parRed_arg`, and `howe_fix`.
Consumers: the S36-style Leibniz law `subst_one_parRed_le`, the
structural containment `one_le_parRed`, the converse-side compatibility
`cr_parRed_converse_le` (M3), every branch of the substitutivity pass
`parRed_subst_le` (H15), and multiple sub-steps of `diamond_parRed`
(the (1,1) corner directly; other corners through M3). -/
theorem cr_parRed_le (a : α) : SRA.cr (parRed a) ≤ parRed a := by
  unfold parRed
  calc SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1))
      = SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1)) * 1 := (mul_one _).symm
    _ ≤ SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1)) * (1 ⊔ SRA.subst a 1) :=
        mul_le_mul_right (one_le_parRed_arg a) _
    _ = SRA.howe (1 ⊔ SRA.subst a 1) := (SRA.howe_fix _).symm

/-- Structural induction (SRA axiom `one_le_of_scr_sup_le` / derived
`one_le_of_cr_le`) lifted through `parRed`: `1 ≤ a⇛`. Direct corollary
of `cr_parRed_le`.

Not used by the current proof of Thm. 21; the only consumer is
`parRed_arg_le_parRed`, which is itself only kept for independent
interest. -/
theorem one_le_parRed (a : α) : (1 : α) ≤ parRed a :=
  SRA.one_le_of_cr_le (cr_parRed_le a)

/-- **Leibniz at parRed.** `1[a⇛] ≤ a⇛`: `parRed a` is closed under
substituting the monoid identity. Immediate from S36
(`SRA.subst_one_le_of_cr_le`) and `cr_parRed_le`. Consumed by
`nesting` and, via M4 (`subst_one_parRed_converse_le`), by M5
(`co_nesting`) in the diamond argument; also enters the substitutivity
pass (`parRed_subst_le`, LICS'23 Prop. 10). -/
theorem subst_one_parRed_le (a : α) : SRA.subst 1 (parRed a) ≤ parRed a :=
  SRA.subst_one_le_of_cr_le (cr_parRed_le a)

/-- The reflexive substitution closure of `a` sits below `parRed a`:
`1 ⊔ a[1] ≤ a⇛`. Combines `one_le_parRed` (giving `1 ≤ cr (a⇛)` via
`cr_one` and `cr_mono`) with `howe_fix`.

Not used by the current proof of Thm. 21; kept as a derived law of
independent interest. -/
theorem parRed_arg_le_parRed (a : α) : (1 ⊔ SRA.subst a 1 : α) ≤ parRed a := by
  unfold parRed
  calc (1 ⊔ SRA.subst a 1 : α)
      = 1 * (1 ⊔ SRA.subst a 1) := (one_mul _).symm
    _ ≤ SRA.cr (SRA.howe (1 ⊔ SRA.subst a 1)) * (1 ⊔ SRA.subst a 1) :=
        mul_le_mul_left
          (SRA.cr_one.ge.trans (SRA.cr_mono (one_le_parRed a))) _
    _ = SRA.howe (1 ⊔ SRA.subst a 1) := (SRA.howe_fix _).symm

/-! ### Substitutivity of `parRed` (H15)

Substitutivity of parallel reduction is stated as Gavazzo LICS'23
Prop. 10 and proved here as an independent result. It is *not* on the
critical path of the diamond theorem (`diamond_parRed` routes through
`nesting` instead — see the note on `nesting`).

As recorded in the module Contents, the naive Howe induction has two
circular joints; both are broken by the paper's standing hypothesis
that the reduction has no variable LHS (`IsReduction`, LICS'23 Rem. 5
/ LICS'26 Def. 17). The two lemmas below capture the two forms in
which the hypothesis is consumed; the main theorem `parRed_subst_le`
then goes through by the plain Howe induction. -/

/-- **L0 — left factorisation via the reduction hypothesis.** For a
reduction `a`, the identity factors on the left as `a = ẽ 1 * a`. Proof:
write
`1 = Δη ⊔ ẽ 1` (SRA axiom `varDiag_sup_scr_one_eq`), distribute over
the product (`Quantale.sup_mul_distrib`), and use the reduction
hypothesis `Δη * a = ⊥` to eliminate the variable branch. Threaded into
`varDiag_mul_subst_one_eq_bot` below. -/
theorem factor_scr_of_isReduction {a : α} (h : IsReduction a) :
    a = SRA.scr 1 * a := by
  have h' : SRA.varDiag * a = (⊥ : α) := h
  calc a
      = 1 * a := (one_mul _).symm
    _ = (SRA.varDiag ⊔ SRA.scr 1) * a := by
        rw [SRA.varDiag_sup_scr_one_eq]
    _ = SRA.varDiag * a ⊔ SRA.scr 1 * a := Quantale.sup_mul_distrib
    _ = ⊥ ⊔ SRA.scr 1 * a := by rw [h']
    _ = SRA.scr 1 * a := bot_sup_eq _

/-- **L1 — reduction is preserved by base substitution.** For a
reduction `a`, `Δη * a[1] = ⊥`: substituting the identity does not turn
a compound-LHS rule into a variable-LHS one. This is the precise point
where `IsReduction` breaks the circularity that stalled the
substitutivity pass (see the H15 entry in the Contents block).

Route: from L0 (`factor_scr_of_isReduction`, `a = ẽ 1 * a`) we lift to
`a[1] ≤ ẽ 1 * a[1]` via `subst_mul_le`, `subst_scr_le`, and S24
(`subst_one_one`). Sandwich with `SRA.varDiag_mul_scr_le_bot` (variables
and compounds are disjoint) and `Quantale.bot_mul`. -/
theorem varDiag_mul_subst_one_eq_bot {a : α} (h : IsReduction a) :
    SRA.varDiag * SRA.subst a 1 = ⊥ := by
  refine le_antisymm ?_ bot_le
  have key : SRA.subst a 1 ≤ SRA.scr 1 * SRA.subst a 1 :=
    calc SRA.subst a 1
        = SRA.subst (SRA.scr 1 * a) (1 * 1) := by
            rw [← factor_scr_of_isReduction h, mul_one]
      _ ≤ SRA.subst (SRA.scr 1) 1 * SRA.subst a 1 := SRA.subst_mul_le _ _ _ _
      _ ≤ SRA.scr (SRA.subst 1 1) * SRA.subst a 1 :=
            mul_le_mul_left (SRA.subst_scr_le _ _) _
      _ = SRA.scr 1 * SRA.subst a 1 := by rw [SRA.subst_one_one]
  calc SRA.varDiag * SRA.subst a 1
      ≤ SRA.varDiag * (SRA.scr 1 * SRA.subst a 1) := mul_le_mul_right key _
    _ = SRA.varDiag * SRA.scr 1 * SRA.subst a 1 := (mul_assoc _ _ _).symm
    _ ≤ ⊥ * SRA.subst a 1 :=
          mul_le_mul_left (SRA.varDiag_mul_scr_le_bot _) _
    _ = ⊥ := Quantale.bot_mul

/-- **H15 — substitutivity of parallel reduction, for reductions.**
`a⇛[a⇛] ≤ a⇛` whenever `a` is a reduction. This is Gavazzo LICS'23
Prop. 10 — a theorem in its own right, not a lemma toward the diamond
(the current proof of `diamond_parRed` goes through `nesting`, not
substitutivity). We keep it as an independent result; the
`IsReduction` diagnosis attaches here. The reduction hypothesis is
*not* removable — a preliminary attempt without it hit two independent
circularities in the Howe induction (`a[rᴴ] ≤ rᴴ` unfolds to the main
goal; the product needs transitivity `rᴴ * rᴴ ≤ rᴴ`, which reduces to
the same substitutivity question one level up). Both papers assume it
(Rem. 5 / Def. 17); the hypothesis is consumed in
`varDiag_mul_subst_one_eq_bot`.

Proof outline. Adjunction / Howe induction / adjunction reduce the goal
to `(cr X * r)[rᴴ] ≤ rᴴ` where `X := rᴴ » rᴴ`, `r := 1 ⊔ a[1]`.
Distribute `cr X * r` and kill the `Δη * a[1]` summand via
`varDiag_mul_subst_one_eq_bot`; the LHS collapses to
`Δη ⊔ ẽ X ⊔ ẽ X * a[1]`. `subst_sup_left` splits into three branches:
`Δη[rᴴ] = rᴴ`; `(ẽ X)[rᴴ]` refines to `ẽ rᴴ ≤ cr rᴴ ≤ rᴴ` via
`subst_scr_le`, the residual adjunction, `cr_parRed_le`; the mixed
branch `(ẽ X * a[1])[rᴴ]` factors through `rᴴ = rᴴ * 1`, uses
`subst_assoc` + S24 on the right, the same `ẽ X` collapse on the left,
and closes with `howe_fix`. -/
theorem parRed_subst_le {a : α} (h : IsReduction a) :
    SRA.subst (parRed a) (parRed a) ≤ parRed a := by
  refine SRA.subst_le_iff.mpr ?_
  refine SRA.howe_le_of_cr_mul_le ?_
  refine SRA.subst_le_iff.mp ?_
  have hrw :
      SRA.cr (parRed a » parRed a) * (1 ⊔ SRA.subst a 1)
        = SRA.varDiag ⊔ SRA.scr (parRed a » parRed a)
            ⊔ SRA.scr (parRed a » parRed a) * SRA.subst a 1 := by
    unfold SRA.cr
    rw [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
        Quantale.mul_sup_distrib, mul_one, mul_one,
        varDiag_mul_subst_one_eq_bot h, sup_bot_eq, ← sup_assoc]
  rw [hrw, SRA.subst_sup_left, SRA.subst_sup_left]
  refine sup_le (sup_le ?_ ?_) ?_
  -- S1: Δη[rᴴ] = rᴴ ≤ rᴴ.
  · exact le_of_eq (SRA.subst_varDiag_left _)
  -- S2: (ẽ X)[rᴴ] ≤ rᴴ.
  · calc SRA.subst (SRA.scr (parRed a » parRed a)) (parRed a)
        ≤ SRA.scr (SRA.subst (parRed a » parRed a) (parRed a)) :=
          SRA.subst_scr_le _ _
      _ ≤ SRA.scr (parRed a) := SRA.scr_mono (SRA.subst_le_iff.mpr le_rfl)
      _ ≤ SRA.cr (parRed a) := le_sup_right
      _ ≤ parRed a := cr_parRed_le a
  -- S3: (ẽ X * a[1])[rᴴ] ≤ rᴴ.
  · calc SRA.subst (SRA.scr (parRed a » parRed a) * SRA.subst a 1)
            (parRed a)
        = SRA.subst (SRA.scr (parRed a » parRed a) * SRA.subst a 1)
            (parRed a * 1) := by rw [mul_one]
      _ ≤ SRA.subst (SRA.scr (parRed a » parRed a)) (parRed a)
            * SRA.subst (SRA.subst a 1) 1 :=
            SRA.subst_mul_le _ _ _ _
      _ = SRA.subst (SRA.scr (parRed a » parRed a)) (parRed a)
            * SRA.subst a 1 := by
            rw [SRA.subst_assoc, SRA.subst_one_one]
      _ ≤ SRA.cr (parRed a) * SRA.subst a 1 := by
          refine mul_le_mul_left ?_ _
          calc SRA.subst (SRA.scr (parRed a » parRed a)) (parRed a)
              ≤ SRA.scr (SRA.subst (parRed a » parRed a) (parRed a)) :=
                SRA.subst_scr_le _ _
            _ ≤ SRA.scr (parRed a) :=
                SRA.scr_mono (SRA.subst_le_iff.mpr le_rfl)
            _ ≤ SRA.cr (parRed a) := le_sup_right
      _ ≤ SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
          mul_le_mul_right le_sup_right _
      _ = parRed a := (SRA.howe_fix _).symm

/-! ### Converse and nesting of `parRed`

Two general-purpose calculations feeding the diamond argument
(`diamond_parRed` below). `parRed_converse` rewrites `(a⇛)ᵒ` into the
op-Howe form, whose fixed-point law reverses the multiplication side
(see `opHowe_fix`), letting a single `rw` swap between the two
half-fixed-points. `nesting` is Gavazzo LICS'23 Lemma 3
(`aᵒ[a⇛] ≤ a⇛ * aᵒ[1]`), stated for `parRed` but proved *without*
invoking `parRed_subst_le`: here the direct route through
`subst_mul_le` and `subst_one_parRed_le` (Leibniz at parRed) suffices.
The paper derives Lemma 3 from substitutivity to keep the argument
uniform for `SF`; we prefer the direct route. -/

/-- **Converse of parallel reduction.** `(a⇛)ᵒ = §(1 ⊔ aᵒ[1])` — the
converse of `parRed a` is the op-Howe extension of the reflexive
substitution closure of `aᵒ`. Direct computation from `howe_converse`
and `converse_sup` / `converse_one` / `subst_converse`, so *not* the
`parRed` of `aᵒ` (that is `howe (1 ⊔ aᵒ[1])`, not `opHowe (…)`) — the
distinction is exactly the left/right asymmetry of the Howe recursor
noted in `Derived.lean`. -/
theorem parRed_converse (a : α) :
    (parRed a)ᵒ = SRA.opHowe (1 ⊔ SRA.subst aᵒ 1) := by
  unfold parRed
  rw [SRA.howe_converse, IsInvolutiveQuantale.converse_sup,
      IsInvolutiveQuantale.converse_one, SRA.subst_converse,
      IsInvolutiveQuantale.converse_one]

/-- **Nesting (Gavazzo LICS'23 Lemma 3).** `aᵒ[a⇛] ≤ a⇛ * aᵒ[1]`:
a converse-`a` substitution into parallel reduction is bounded by
parallel reduction post-composed with a base converse instance.

The paper derives this from substitutivity; we take the direct route
via `subst_mul_le` and `subst_one_parRed_le` (Leibniz at parRed), so
`parRed_subst_le` and hence `IsReduction` are *not* required. -/
theorem nesting (a : α) :
    SRA.subst aᵒ (parRed a) ≤ parRed a * SRA.subst aᵒ 1 := by
  calc SRA.subst aᵒ (parRed a)
      = SRA.subst (1 * aᵒ) (parRed a * 1) := by rw [one_mul, mul_one]
    _ ≤ SRA.subst 1 (parRed a) * SRA.subst aᵒ 1 := SRA.subst_mul_le _ _ _ _
    _ ≤ parRed a * SRA.subst aᵒ 1 :=
        mul_le_mul_left (subst_one_parRed_le a) _

/-! ### Micro-lemmas for the diamond argument

Small named results extracted so `diamond_parRed`'s 2×2 case matrix
stays readable. Each is one to three lines; nothing subtle happens
here — the subtlety is in choosing the *induction side* (see the
`diamond_parRed` docstring) and how these compose. -/

/-- **M1.** `(a[1])ᵒ = aᵒ[1]`: converse commutes with base substitution.
`subst_converse` then `converse_one`. -/
theorem subst_one_converse (a : α) : (SRA.subst a 1)ᵒ = SRA.subst aᵒ 1 := by
  rw [SRA.subst_converse, IsInvolutiveQuantale.converse_one]

/-- **M2.** Converse of `varDiag_mul_subst_one_eq_bot`: `aᵒ[1] * Δη = ⊥`
for a reduction `a`. Ships the same "no variable on this side" content,
mirrored. -/
theorem subst_one_mul_varDiag_eq_bot {a : α} (h : IsReduction a) :
    SRA.subst aᵒ 1 * SRA.varDiag = (⊥ : α) := by
  have hL := varDiag_mul_subst_one_eq_bot h
  have := congrArg IsInvolutiveQuantale.converse hL
  rw [IsInvolutiveQuantale.mul_converse, subst_one_converse,
      SRA.varDiag_converse, IsInvolutiveQuantale.converse_bot] at this
  exact this

/-- **M3.** `(a⇛)ᵒ` is compatibility-closed: `((a⇛)ᵒ)ˆ ≤ (a⇛)ᵒ`.
Converse of `cr_parRed_le` via `cr_converse`. -/
theorem cr_parRed_converse_le (a : α) : SRA.cr ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  rw [← SRA.cr_converse]
  exact IsInvolutiveQuantale.converse_le_converse (cr_parRed_le a)

/-- **M4.** Leibniz at `(a⇛)ᵒ`: `1[(a⇛)ᵒ] ≤ (a⇛)ᵒ`. Converse-and-back
of `subst_one_parRed_le`. -/
theorem subst_one_parRed_converse_le (a : α) :
    SRA.subst 1 ((parRed a)ᵒ) ≤ (parRed a)ᵒ :=
  SRA.subst_one_le_of_cr_le (cr_parRed_converse_le a)

/-- **M5 — Co-nesting.** `a[(a⇛)ᵒ] ≤ a[1] * (a⇛)ᵒ`. Same architecture as
`nesting`: `subst_mul_le` on `a = 1 * a` and `(a⇛)ᵒ = (a⇛)ᵒ * 1`, then
Leibniz `subst_one_parRed_converse_le` (M4). -/
theorem co_nesting (a : α) :
    SRA.subst a ((parRed a)ᵒ) ≤ SRA.subst a 1 * (parRed a)ᵒ := by
  calc SRA.subst a ((parRed a)ᵒ)
      = SRA.subst (a * 1) (1 * (parRed a)ᵒ) := by rw [mul_one, one_mul]
    _ ≤ SRA.subst a 1 * SRA.subst 1 ((parRed a)ᵒ) := SRA.subst_mul_le _ _ _ _
    _ ≤ SRA.subst a 1 * (parRed a)ᵒ :=
        mul_le_mul_right (subst_one_parRed_converse_le a) _

/-- **M6.** `(a⇛)ˆ * a[1] ≤ a⇛`. The S3 sub-bound of `parRed_subst_le`,
extracted: weaken `a[1]` to `1 ⊔ a[1]` and close by `howe_fix`. -/
theorem cr_mul_subst_le_parRed (a : α) :
    SRA.cr (parRed a) * SRA.subst a 1 ≤ parRed a :=
  calc SRA.cr (parRed a) * SRA.subst a 1
      ≤ SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
        mul_le_mul_right le_sup_right _
    _ = parRed a := (SRA.howe_fix _).symm

/-- **M8.** Converse of M6: `aᵒ[1] * ((a⇛)ᵒ)ˆ ≤ (a⇛)ᵒ`. First
appeared in the `ẽ` form `aᵒ[1] * (ẽ(a⇛))ᵒ ≤ (a⇛)ᵒ` while proving
`parRed_subst_le`; generalised here to `ˆ` in place of `ẽ` (still
holds because `Δη ≤ (a⇛)ᵒ`), which is the form the diamond argument
needs. -/
theorem subst_one_mul_cr_parRed_converse_le (a : α) :
    SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ) ≤ (parRed a)ᵒ := by
  have hM6 := cr_mul_subst_le_parRed a
  have := IsInvolutiveQuantale.converse_le_converse hM6
  rw [IsInvolutiveQuantale.mul_converse, subst_one_converse,
      SRA.cr_converse] at this
  exact this

/-- `a` is *orthogonal* when its base substitution instances collapse on
overlaps in two senses, capturing determinism-modulo-variable-renaming:

1. `(a[1])ᵒ * a[1] ≤ 1` — two `a`-rewrites of the same term differ only
   by variable renaming.
2. `(a[1])ᵒ * ẽ(a⇛) ≤ aᵒ[a⇛]` — a base-instance backwards step followed
   by a strict compatible refinement of parallel reduction can be
   swapped for a substituted converse.

Gavazzo LICS'23 Def. 12 gives orthogonality for `a^SP` (parallel
reduction); it is Theorem 6 of the same paper that restates it for
`a^SF` (the Howe/full reduction), and it is that restatement that we
transcribe here, with `SF` replaced by our `parRed`.

Reading of the second conjunct. The LICS'26 typography of Thm. 21 is
ambiguous between the strict compatible refinement `ẽ` and the full
one `ˆ`. We read it as strict, confirmed by cross-checking LICS'23
Thm. 6, which spells the same conjunct as `a[∆]◦ ; ã^SF ≤ a◦[a^SF]`
(the tilde on `a^SF` is the strict variant). The strict reading also
gives the *weaker* hypothesis (`ẽ ≤ ˆ`), and hence the *stronger*
theorem.

`diamond_parRed` carries `(h : IsReduction a)` alongside
`IsOrthogonal a`, consistent with LICS'23 Rem. 5 / LICS'26 Def. 17 —
every rule under consideration is a reduction, and `parRed_subst_le`
(H15) already depends on it. -/
def IsOrthogonal (a : α) : Prop :=
  (SRA.subst a 1)ᵒ * SRA.subst a 1 ≤ 1
    ∧ (SRA.subst a 1)ᵒ * SRA.scr (parRed a) ≤ SRA.subst aᵒ (parRed a)

/-! ### Diamond and confluence -/

/-- **M7.** Converse form of `horth.2`: `ẽ((a⇛)ᵒ) * a[1] ≤ a[(a⇛)ᵒ]`.
Take the converse of `horth.2` — using `mul_converse`, M1, `subst_converse`,
and `scr_converse` to move each factor across `·ᵒ`. -/
theorem scr_parRed_converse_mul_le {a : α} (horth : IsOrthogonal a) :
    SRA.scr ((parRed a)ᵒ) * SRA.subst a 1 ≤ SRA.subst a ((parRed a)ᵒ) := by
  have h2 := horth.2
  have := IsInvolutiveQuantale.converse_le_converse h2
  rw [IsInvolutiveQuantale.mul_converse, IsInvolutiveQuantale.converse_involutive,
      SRA.subst_converse, IsInvolutiveQuantale.converse_involutive,
      ← SRA.scr_converse] at this
  exact this

/-- **Diamond property of parallel reduction** (Gavazzo LICS'23 Thm. 6 /
LICS'26 Thm. 21).  For a reduction `a` that satisfies the orthogonality
conditions, `(a⇛)ᵒ * a⇛ ≤ a⇛ * (a⇛)ᵒ`.

**Induction side.**  A preliminary attempt inducted on the RIGHT
factor — `howe_le_of_cr_mul_le` on `a⇛` — which leaves a trailing `a[1]`
next to the opaque residual, and the determinism conjunct `horth.1`
never finds a matching sub-term.  The paper (LICS'23) inducts on
`(a⇛)ᵒ = §(1 ⊔ aᵒ[1])` via `opHowe_le_of_mul_cr_le` — this rewrites the
`(a⇛)ᵒ` factor from the left, and the trailing `a[1]` ends up sandwiched
between the two endpoints, exactly where `horth.1` (as
`aᵒ[1] * a[1] ≤ 1`) fires.

**Structure.**  The middle collapses by `cr_mul` and the residual defn
into `cr(a⇛) * cr((a⇛)ᵒ)`; the two-sided expansion by
`r' = 1 ⊔ aᵒ[1]` on the left and `r = 1 ⊔ a[1]` on the right yields a
2×2 case matrix over `{1, aᵒ[1]} × {1, a[1]}` — the algebraic form of
the classical parallel-moves case analysis:

* `(1, 1)`: `cr_parRed_le` × `cr_parRed_converse_le` (M3).
* `(1, a[1])`: the `Δη`-summand of `cr((a⇛)ᵒ)` dies by
  `varDiag_mul_subst_one_eq_bot` (L1); the `ẽ`-summand goes through
  M7 → M5 (`co_nesting`); close with M6.
* `(aᵒ[1], 1)`: `Δη` dies by M2; `ẽ` goes through `horth.2` (via M1)
  → `nesting` → M8.
* `(aᵒ[1], a[1])` — **the critical corner**: `horth.2` → `nesting`
  → M7 → M5 → `horth.1` (via M1) collapses the sandwich
  `aᵒ[1] * a[1]` to `1`. -/
theorem diamond_parRed {a : α} (h : IsReduction a) (horth : IsOrthogonal a) :
    Diamond (parRed a) := by
  change (parRed a)ᵒ * parRed a ≤ parRed a * (parRed a)ᵒ
  refine Quantale.leftMulResiduation_le_iff_mul_le.mp ?_
  rw [parRed_converse a]
  refine SRA.opHowe_le_of_mul_cr_le ?_
  rw [← parRed_converse a]
  refine Quantale.leftMulResiduation_le_iff_mul_le.mpr ?_
  -- Middle collapse:
  --   cr U * cr(a⇛) = cr(U * a⇛) ≤ cr(a⇛ * (a⇛)ᵒ) = cr(a⇛) * cr((a⇛)ᵒ).
  have hU : (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a
              ≤ parRed a * (parRed a)ᵒ :=
    Quantale.leftMulResiduation_le_iff_mul_le.mp le_rfl
  have hmid :
      SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a)
        ≤ SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) := by
    calc SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a)
        = SRA.cr ((parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * parRed a) :=
            SRA.cr_mul _ _
      _ ≤ SRA.cr (parRed a * (parRed a)ᵒ) := SRA.cr_mono hU
      _ = SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) := (SRA.cr_mul _ _).symm
  -- Left side-bound: aᵒ[1] * cr(a⇛) ≤ a⇛ * aᵒ[1].
  have Hleft :
      SRA.subst aᵒ 1 * SRA.cr (parRed a) ≤ parRed a * SRA.subst aᵒ 1 := by
    unfold SRA.cr
    rw [Quantale.mul_sup_distrib]
    refine sup_le ?_ ?_
    · calc SRA.subst aᵒ 1 * SRA.varDiag
          = (⊥ : α) := subst_one_mul_varDiag_eq_bot h
        _ ≤ parRed a * SRA.subst aᵒ 1 := bot_le
    · have h2 := horth.2
      rw [subst_one_converse] at h2
      exact h2.trans (nesting a)
  -- Right side-bound: cr((a⇛)ᵒ) * a[1] ≤ a[1] * (a⇛)ᵒ.
  have Hright :
      SRA.cr ((parRed a)ᵒ) * SRA.subst a 1
        ≤ SRA.subst a 1 * (parRed a)ᵒ := by
    unfold SRA.cr
    rw [Quantale.sup_mul_distrib]
    refine sup_le ?_ ?_
    · calc SRA.varDiag * SRA.subst a 1
          = (⊥ : α) := varDiag_mul_subst_one_eq_bot h
        _ ≤ SRA.subst a 1 * (parRed a)ᵒ := bot_le
    · exact (scr_parRed_converse_mul_le horth).trans (co_nesting a)
  -- Horth.1 in aᵒ-form.
  have Hdet : SRA.subst aᵒ 1 * SRA.subst a 1 ≤ (1 : α) := by
    have h1 := horth.1
    rw [subst_one_converse] at h1
    exact h1
  -- Expand the trailing a⇛ via howe_fix (rewriting only the outer
  -- multiplier — the 4th `parRed a` occurrence in the goal).
  have hfix : parRed a = SRA.cr (parRed a) * (1 ⊔ SRA.subst a 1) :=
    SRA.howe_fix _
  nth_rewrite 4 [hfix]
  -- Regroup so the middle two factors are cr U * cr(a⇛).
  rw [show ∀ A B C D : α, A * B * (C * D) = A * (B * C) * D from
        fun _ _ _ _ => by simp only [mul_assoc]]
  calc (1 ⊔ SRA.subst aᵒ 1)
          * (SRA.cr (parRed a ⇨ₗ (parRed a * (parRed a)ᵒ)) * SRA.cr (parRed a))
          * (1 ⊔ SRA.subst a 1)
      ≤ (1 ⊔ SRA.subst aᵒ 1)
          * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
          * (1 ⊔ SRA.subst a 1) :=
          mul_le_mul_left (mul_le_mul_right hmid _) _
    _ ≤ parRed a * (parRed a)ᵒ := ?_
  -- Distribute the two `1 ⊔ ·` factors into four corners.
  simp only [Quantale.sup_mul_distrib, Quantale.mul_sup_distrib,
             one_mul, mul_one]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  -- Corner (1, 1): cr(a⇛) * cr((a⇛)ᵒ) ≤ a⇛ * (a⇛)ᵒ.
  · exact mul_le_mul' (cr_parRed_le a) (cr_parRed_converse_le a)
  -- Corner (aᵒ[1], 1): aᵒ[1] * (cr(a⇛) * cr((a⇛)ᵒ)) ≤ a⇛ * (a⇛)ᵒ.
  · calc SRA.subst aᵒ 1 * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
        = SRA.subst aᵒ 1 * SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) :=
            (mul_assoc _ _ _).symm
      _ ≤ parRed a * SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ) :=
            mul_le_mul_left Hleft _
      _ = parRed a * (SRA.subst aᵒ 1 * SRA.cr ((parRed a)ᵒ)) := mul_assoc _ _ _
      _ ≤ parRed a * (parRed a)ᵒ :=
            mul_le_mul_right (subst_one_mul_cr_parRed_converse_le a) _
  -- Corner (1, a[1]): cr(a⇛) * cr((a⇛)ᵒ) * a[1] ≤ a⇛ * (a⇛)ᵒ.
  · calc SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ) * SRA.subst a 1
        = SRA.cr (parRed a) * (SRA.cr ((parRed a)ᵒ) * SRA.subst a 1) :=
            mul_assoc _ _ _
      _ ≤ SRA.cr (parRed a) * (SRA.subst a 1 * (parRed a)ᵒ) :=
            mul_le_mul_right Hright _
      _ = SRA.cr (parRed a) * SRA.subst a 1 * (parRed a)ᵒ :=
            (mul_assoc _ _ _).symm
      _ ≤ parRed a * (parRed a)ᵒ :=
            mul_le_mul_left (cr_mul_subst_le_parRed a) _
  -- Corner (aᵒ[1], a[1]) — the CRITICAL corner. horth.1 fires here.
  · calc SRA.subst aᵒ 1 * (SRA.cr (parRed a) * SRA.cr ((parRed a)ᵒ))
            * SRA.subst a 1
        = (SRA.subst aᵒ 1 * SRA.cr (parRed a))
            * (SRA.cr ((parRed a)ᵒ) * SRA.subst a 1) := by
            simp only [mul_assoc]
      _ ≤ (parRed a * SRA.subst aᵒ 1) * (SRA.subst a 1 * (parRed a)ᵒ) :=
            mul_le_mul' Hleft Hright
      _ = parRed a * (SRA.subst aᵒ 1 * SRA.subst a 1) * (parRed a)ᵒ := by
            simp only [mul_assoc]
      _ ≤ parRed a * 1 * (parRed a)ᵒ :=
            mul_le_mul_left (mul_le_mul_right Hdet _) _
      _ = parRed a * (parRed a)ᵒ := by rw [mul_one]

/-- **Confluence of parallel reduction.** Immediate `Diamond.confluent`
of `diamond_parRed`; `Confluent (parRed a)`, i.e. `Diamond ((parRed a)∗)`. -/
theorem confluent_parRed {a : α} (h : IsReduction a) (horth : IsOrthogonal a) :
    Confluent (parRed a) :=
  (diamond_parRed h horth).confluent

end LeanTra.Confluence

#print axioms SRA.subst_one_one
#print axioms SRA.subst_one_le_of_cr_le
#print axioms SRA.howe_converse
#print axioms LeanTra.Confluence.parRed_subst_le
#print axioms LeanTra.Confluence.diamond_parRed
#print axioms LeanTra.Confluence.confluent_parRed
