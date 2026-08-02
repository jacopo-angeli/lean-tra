/-
Master's thesis — Lean 4 formalisation of Term Relation Algebras.
Author: Jacopo Angeli.
-/
module

public import LeanTra.Instances.FirstOrder.SRA
public import LeanTra.Confluence.Orthogonal

/-!
# Confluence of orthogonal reduction on first-order terms

`Confluence/Orthogonal.lean` proves `confluent_parRed` for an arbitrary
`[SRA α]`: whenever `a` is a reduction (`Δη * a = ⊥`) and satisfies the
two orthogonality conjuncts, its parallel reduction `a⇛` is confluent
(LICS'26 Theorem 21). Phase C (`Instances/FirstOrder/SRA.lean`)
discharges the sixteen `SRA` axioms on the carrier `SynRel S`. This
file records the immediate corollary: the same theorem holds on the
first-order term model, for every `φ : SynRel S` verifying the same
two local hypotheses.

Nothing new is proved here. The abstract theorem is stated over an
arbitrary `[SRA α]`; the term model is such an `α`; the instantiation
is a direct application. The file exists to name the corollary and to
close the loop between Phase C and the confluence chapter — a payoff
of the point-free formulation.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026, Theorem 21.
-/
@[expose] public section

namespace LeanTra.Instances.FirstOrder

variable {S : Signature}

/-- Confluence of orthogonal reduction on the first-order term model.
Direct instantiation of `LeanTra.Confluence.confluent_parRed` at the
`SRA (SynRel S)` instance built in Phase C. -/
theorem confluent_parRed_synRel {φ : SynRel S}
    (h : LeanTra.Confluence.IsReduction φ)
    (horth : LeanTra.Confluence.IsOrthogonal φ) :
    LeanTra.Confluence.Confluent (LeanTra.Confluence.parRed φ) :=
  LeanTra.Confluence.confluent_parRed h horth

end LeanTra.Instances.FirstOrder

#print axioms LeanTra.Instances.FirstOrder.confluent_parRed_synRel
