import Allegory.TRA.Modalities
import Allegory.TRA.Similarity.HoweExtension
import Allegory.TRA.Similarity.Basic

/-!
# Paper notation

Centralises the Unicode notations used by Gavazzo, LICS 2026, so that Lean
files can be read alongside the paper. Each notation aliases an existing
definition; nothing new is introduced. Importing this module is optional and
purely cosmetic — every theorem in `Allegory/*` is statable without it.

The notations cover the four families that appear most often in the paper:
the substitution monoid (`Δη`, `_[_]`, `˜_`), the modalities (`□`, `♦`, `♢`),
the Howe / op-Howe extensions (`_ᴴ`, `_§`), and the simulation hierarchy
(`B(_)`, `_⪆`, `_=∼`).

## References

* Gavazzo, *An Algebraic Approach to Formal System Metatheory*, LICS 2026
-/

open CategoryTheory

namespace Allegory.TRA

/-! ## Substitution monoid -/

/-- Paper `Δη` — substitution unit (variable coreflexive). -/
scoped notation "Δη" => Allegory.TRA.delta_eta

/-- Paper `Δκ` — value coreflexive `□Δ`. -/
scoped notation "Δκ" => Allegory.TRA.delta_kappa

/-- Paper `R[S]` — substitution `R[S]`. -/
scoped notation:80 R "[" S "]" => Allegory.TRA.substitution R S

/-- Paper `˜R` — semirelator / Howe extension on a single morphism. -/
scoped prefix:90 "˜" => Allegory.TRA.tilde

/-! ## Modalities -/

/-- Paper `□a` — closing modality `a[⊥]`. -/
scoped prefix:90 "□" => Allegory.TRA.box

/-- Paper `♦a` — right-adjoint modality `a » ⊥`. -/
scoped prefix:90 "♦" => Allegory.TRA.diamond

/-- Paper `♢a` — open extension `Δ » ♦a`. -/
scoped prefix:90 "♢" => Allegory.TRA.openExt

/-! ## Howe / op-Howe -/

/-- Paper `aᴴ` — Howe closure of `a`. -/
scoped postfix:90 "ᴴ" => Allegory.TRA.howe

/-- Paper `a§` — op-Howe extension of `a`. -/
scoped postfix:90 "§" => Allegory.TRA.opHowe

/-! ## Simulation hierarchy -/

/-- Paper `B(a)` parameterised by candidate `b` — simulation functional. -/
scoped notation "B[" b "](" a ")" => Allegory.TRA.simulationFunctional b a

/-- Paper `b⪆` — similarity (the gfp of `B(♢·)`). -/
scoped postfix:90 "⪆" => Allegory.TRA.similarity

/-- Paper `b=∼` — bisimilarity. -/
scoped postfix:90 "=∼" => Allegory.TRA.bisimilarity

end Allegory.TRA
