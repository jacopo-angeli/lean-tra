# Project Architecture Prompt — Allegories and Term Relation Algebras in Lean 4

## Context

This is a master's thesis formalization (Università di Padova, supervisor: Prof. Francesco Gavazzo)
of the theory of allegories and Term Relation Algebras (TRA), following:
- Gavazzo, *Allegories of Symbolic Manipulations*, LICS 2023
- Ferro, *Towards a Relational Theory of Meaning*, Padova 2024/25
- Freyd–Scedrov, *Categories, Allegories*, 1990

It is the first mechanized formalization of this material in Lean 4 (not in Mathlib).
The project also documents LLM-assisted formalization methodology.

---

## Mathlib Anchor Points (verified in the installed version)

Before writing any file, understand which Mathlib APIs are used as foundations.

### Order theory
- `Mathlib.Order.GaloisConnection.Defs`
  - `GaloisConnection l u := ∀ a b, l a ≤ b ↔ a ≤ u b` (a `def`, not a class)
- `Mathlib.Order.FixedPoints`
  - `OrderHom.lfp : (α →o α) →o α` (least fixed point for `CompleteLattice`)
  - `OrderHom.gfp : (α →o α) →o α` (greatest fixed point)
  - Key lemmas: `lfp_le`, `lfp_le_fixed`, `lfp_induction`, `le_gfp`, `gfp_induction`, `lfp_le_gfp`
- `Mathlib.Order.OmegaCompletePartialOrder`
  - `OmegaCompletePartialOrder` — class extending `PartialOrder` with `ωSup : Chain α → α`
  - `Chain α` — a `structure` extending `ℕ →o α`
  - `ωScottContinuous f` — `f` preserves `ωSup` of chains
  - Every `CompleteLattice` is an `OmegaCompletePartialOrder`
- `Mathlib.Order.CompleteLattice` — `CompleteLattice`, `sSup`, `sInf`, `iSup`, `iInf`
- `Mathlib.Order.BoundedOrder.Lattice` — `Lattice`, `BoundedOrder`, `⊥`, `⊤`

### Category theory
- `Mathlib.CategoryTheory.Category.Basic` — `Category`, `𝟙`, `≫`
- `Mathlib.CategoryTheory.Functor.Basic` — `Functor` (`⥤`), `𝟭`, `⋙`
- `Mathlib.CategoryTheory.Monad.Basic`
  - `Monad` — structure extending `C ⥤ C` with `η : 𝟭 ⟶ T`, `μ : T ⋙ T ⟶ T`
  - `Comonad` — dual
- `Mathlib.CategoryTheory.Monad.Algebra`
  - `Monad.Algebra T` — structure with `A : C`, `a : T.obj A ⟶ A` and coherence laws
  - `Monad.Algebra.Hom` — algebra homomorphisms
  - **No `InitialAlgebra` in Mathlib** — must be defined custom as:
    ```lean
    structure InitialAlgebra (T : Monad C) extends Monad.Algebra T where
      initial : ∀ (B : Monad.Algebra T), Nonempty (Monad.Algebra.Hom toAlgebra B)
      unique   : ∀ (B : Monad.Algebra T) (f g : Monad.Algebra.Hom toAlgebra B), f = g
    ```

---

## Coding and Documentation Conventions

These apply to every file in the project without exception.

### Naming
- All identifiers: English, `snake_case`, descriptive
- Type parameters: `A`, `B`, `C` for allegory/RA types; `α`, `β` for order-theoretic types
- Scoped notations declared with `scoped[<Namespace>] notation/infix/postfix`
- `@[simp]` only outside class bodies, only on terminating rewrite rules
- `intersection_commutativity` must NOT be `@[simp]` (infinite loop risk — already documented)

### File header (every file)
```lean
/-!
# <Title>

<One paragraph description of what this file formalizes.>

## Main definitions

* `Foo` — ...
* `Bar.baz` — ...

## Main results

* `Foo.theorem_name` — ...

## References

* Author, *Title*, Year, §section
-/
```

### Docstrings
- Every `class`, `structure`, `def`, `theorem`, `instance` gets a `/-- ... -/` docstring
- Docstrings describe the mathematical content and the paper reference when non-obvious
- No inline `--` comments unless documenting a non-obvious proof step or a known Lean pitfall

### Proof style
- All proofs external to class/structure bodies
- Prefer `rw`/`simp`/`exact` chains over `calc` blocks unless the calculation is long
- `sorry` only as an explicit placeholder with a strategy comment immediately above it:
  ```lean
  /- Strategy: use le_antisymm + galois_law -/
  theorem foo : ... := by sorry
  ```

---

## Full Repository Structure

```
allegories/
├── lakefile.lean
├── lean-toolchain
├── lake-manifest.json
├── .github/
│   └── workflows/lean_action_ci.yml
├── Allegories.lean                     ← root index (imports all modules)
└── Allegories/
    │
    │  ── Layer 1: Core allegory infrastructure ──
    ├── Basic.lean                      ✅ COMPLETE
    ├── Lemmas.lean                     ✅ COMPLETE
    ├── Structures.lean                 ✅ COMPLETE
    ├── Maps.lean                       🔲 TODO
    ├── Relator.lean                    ✅ COMPLETE (basic relator)
    ├── ColaxRelator.lean               🔲 TODO
    ├── RelationAlgebra.lean            🟡 IN PROGRESS (6 sorry)
    │
    │  ── Layer 2: Term Relation Algebra ──
    └── TRA/
        ├── Basic.lean                  🔲 TODO  (T1)
        ├── Properties.lean             🔲 TODO  (E1)
        ├── Modalities.lean             🔲 TODO  (E2)
        ├── FixedPointLemmas.lean       🔲 TODO  (E3)
        ├── Harmony.lean                🔲 TODO  (H1)
        ├── Operational/
        │   ├── Decomposition.lean      🔲 TODO  (O1)
        │   ├── GIP.lean                🔲 TODO  (O2)
        │   ├── GCP.lean                🔲 TODO  (O3)
        │   └── FOperator.lean          🔲 TODO  (O4)
        ├── Reduction/
        │   ├── Basic.lean              🔲 TODO  (R1)
        │   ├── ParallelReduction.lean  🔲 TODO  (R2)
        │   ├── Confluence.lean         🔲 TODO  (R3–R5)
        │   └── Orthogonality.lean      🔲 TODO  (R4)
        ├── Evaluation/
        │   ├── BigStep.lean            🔲 TODO  (B1–B3)
        │   └── Determinism.lean        🔲 TODO  (B4)
        ├── Similarity/
        │   ├── Basic.lean              🔲 TODO  (S1)
        │   ├── HoweExtension.lean      🔲 TODO  (S2)
        │   └── Congruence.lean         🔲 TODO  (S3–S4)
        └── Bridge.lean                 🔲 TODO  (M1–M2)

    └── Instances/
        ├── FirstOrder/
        │   └── TRA.lean                🔲 TODO  (I1)
        └── Lambda/
            ├── Terms.lean              🔲 TODO  (I2)
            ├── Operational.lean        🔲 TODO  (I3)
            ├── Beta.lean               🔲 TODO  (I4–I6)
            └── Confluence.lean         🔲 TODO  (I7 — final corollary)
```

---

## File-by-File Specification

### `Allegories/Maps.lean` (new — prerequisite for Structures.lean Prop 3.1.2)

```
Imports: Allegories.Basic, Allegories.Lemmas
Purpose: Define the subcategory Map(A) of an allegory (maps = morphisms f with f°;f ≤ ∆
         and ∆ ≤ f;f°), and the Rel(−) construction. Needed to state Prop 3.1.2.
```

Key definitions:
```lean
/-- `IsMap R` holds when `R` is a map: has a right adjoint equal to its converse. -/
def IsMap {A : Type*} [Allegory A] {X Y : A} (f : X ⟶ Y) : Prop :=
  converse f ≫ f = 𝟙 X ∧ hom_le (𝟙 Y) (f ≫ converse f)
```
Mark with a TODO: full `Map(A)` as a `Category` and the isomorphism `Rel(Map(A)) ≅ A`
require a bundled subcategory construction — defer to after `Structures.lean` is stable.

---

### `Allegories/ColaxRelator.lean` (new — A3 completion)

```
Imports: Allegories.Basic, Allegories.Lemmas, Allegories.Relator
Purpose: The four-level hierarchy of relators needed for TRA.
         Relator (done) → ColaxRelator → Semirelator → ωCocontinuousRelator
```

Key definitions:
```lean
/-- A colax relator is a relator `F` satisfying `F(∆) ≤ₐ ∆` and
`F(a ; b) ≤ₐ F(a) ; F(b)`. This is weaker than a strict relator. -/
structure ColaxRelator (A B : Type*) [Allegory A] [Allegory B]
    extends Relator A B where
  map_id_le     : ∀ (X : A), toRelator.map (𝟙 X) ≤ₐ 𝟙 (toRelator.obj X)
  map_comp_le   : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z),
      toRelator.map (R ≫ S) ≤ₐ toRelator.map R ≫ toRelator.map S

/-- A semirelator is a colax relator where composition is preserved strictly. -/
structure Semirelator (A B : Type*) [Allegory A] [Allegory B]
    extends ColaxRelator A B where
  map_comp_eq  : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z),
      toRelator.map (R ≫ S) = toRelator.map R ≫ toRelator.map S
```

For `ωCocontinuousRelator`: the carrier `A` must be a `LocallyCompleteAllegory` and each
hom-set must carry an `OmegaCompletePartialOrder`. Import:
`Mathlib.Order.OmegaCompletePartialOrder`. The continuity condition is:
```lean
  map_ωSup     : ∀ {X Y : A} (c : Chain (X ⟶ Y)),
      toRelator.map (ωSup c) = ωSup (c.map ⟨toRelator.map, toRelator.map_monotone⟩)
```
(Here `ωSup` comes from the `OmegaCompletePartialOrder` instance on `X ⟶ Y`.)

---

### `Allegories/RelationAlgebra.lean` (in progress — complete the 6 sorry)

The structure is correct. Resolve in this order (each has a known strategy):

1. **`identity_le_star`** — DONE (use as template for others)

2. **`comp_mono_left`** and **`comp_mono_right`** — use `comp_sup_left`/`comp_sup_right`
   combined with the fact that `a ≤ b ↔ a ⊔ b = b` (Mathlib: `sup_eq_right`):
   ```lean
   theorem comp_mono_left (c : A) {a b : A} (h : a ≤ b) : comp a c ≤ comp b c := by
     rw [← sup_eq_right.mpr h, comp_sup_left]
     exact le_sup_right
   ```

3. **`converse_identity`** — use `le_antisymm` with `galois_law`:
   ```lean
   -- ∆° ≤ ∆: apply galois_law with a := ∆°, b := ∆
   --   ∆° ≤ ∆° is le_refl; converse_involution gives ∆°° = ∆
   -- ∆ ≤ ∆°: apply galois_law with a := ∆, b := ∆°
   --   ∆ ≤ ∆ is le_refl
   ```

4. **`converse_sup`** — `le_antisymm`:
   - `(a ⊔ b)° ≤ a° ⊔ b°`: use `galois_law`, `le_sup_left`, `le_sup_right`
   - `a° ⊔ b° ≤ (a ⊔ b)°`: use `sup_le` + `galois_law`

5. **`converse_comp`** — `le_antisymm`:
   - `(a ⊙ b)° ≤ b° ⊙ a°`: use `right_residual_adjunction`, `left_residual_adjunction`
   - `b° ⊙ a° ≤ (a ⊙ b)°`: symmetrically

6. **`star_identity`** — `le_antisymm`:
   - `δ⋆ ≤ δ`: `star_induction_left` with `b := identity`; need `identity ⊔ identity ⊙ identity ≤ identity`
   - `δ ≤ δ⋆`: `identity_le_star`

7. **`star_comp_star_le`** — `star_induction_left` with `b := star a`:
   need `identity ⊔ comp a (star a) ≤ star a`, which is exactly `star_unfold`

---

### `Allegories/TRA/Basic.lean` (T1 — CRITICAL)

```
Imports: Allegories.RelationAlgebra, Allegories.ColaxRelator
Purpose: Central definition of the paper. Ferro Def 4.3.1 / Gavazzo Def. 6.
```

A TRA extends `RelationAlgebra` with:
- A cocartesian semirelator triple `(ẽ·, ∆̃, ·̂)` — the compatible refinement
- A Howe extension operator `init`

Design decision: make `RelationAlgebra` a superclass, and add the TRA structure on top.
Use the standalone `RelationAlgebra` — the connection to `Allegory` comes later via instances.

```lean
open RelationAlgebra

class TermRelationAlgebra (A : Type*) extends RelationAlgebra A where
  /-- Compatible refinement: lifts a relation `a` to `ã`, the smallest compatible
  extension of `a`. -/
  refinement : A → A

  /-- The identity element is fixed by refinement: `∆̃ = ∆`. -/
  refinement_identity : refinement identity = identity
  /-- Refinement is monotone: `a ≤ b → ã ≤ b̃`. -/
  refinement_mono : ∀ {a b : A}, a ≤ b → refinement a ≤ refinement b
  /-- Refinement distributes over composition: `(a ⊙ b)~ = ã ⊙ b̃`. -/
  refinement_comp : ∀ (a b : A), refinement (comp a b) = comp (refinement a) (refinement b)
  /-- Refinement commutes with converse: `(a°)~ = (ã)°`. -/
  refinement_converse : ∀ (a : A), refinement (converse a) = converse (refinement a)
  /-- Refinement commutes with star: `(a⋆)~ = (ã)⋆`. -/
  refinement_star : ∀ (a : A), refinement (star a) = star (refinement a)
  /-- Structural induction: `ã ≤ a → ∆ ≤ a`. -/
  refinement_induction : ∀ (a : A), refinement a ≤ a → identity ≤ a

  /-- Howe extension: `init(a)` is the least solution of `x = x̃ ⊙ a`. -/
  howe : A → A
  /-- Unfolding: `init(a) = init(a)~ ⊙ a`. -/
  howe_unfold : ∀ (a : A), howe a = comp (refinement (howe a)) a
  /-- Left induction: `init(s) ⊙ a ≤ s → init(a) ≤ s`. -/
  howe_induction : ∀ (a s : A), comp (refinement s) a ≤ s → howe a ≤ s
```

Scoped notations:
```lean
scoped[TRA] postfix:90 "~" => TermRelationAlgebra.refinement
scoped[TRA] notation:80 a "ᴴ" => TermRelationAlgebra.howe a
```

---

### `Allegories/TRA/Properties.lean` (E1)

```
Imports: Allegories.TRA.Basic
Purpose: Key predicates on relations used throughout the theory.
```

```lean
/-- `a` is compatible: `a ≤ ã`. -/
def IsCompatible [TRA A] (a : A) : Prop := a ≤ refinement a

/-- `a` is CUI (closed under identity): `a[∆] ≤ a`. -/
def IsCUI [TRA A] (a : A) : Prop := ...  -- requires substitution from TRA definition

/-- `a` is substitutive: `a[a] ≤ a`. -/
def IsSubstitutive [TRA A] (a : A) : Prop := ...

/-- `a` satisfies Leibniz's law: `∆[a] ≤ a`. -/
def IsLeibniz [TRA A] (a : A) : Prop := ...
```

Key theorem: `IsCompatible.implies_reflexive : IsCompatible a → identity ≤ a`
(proof: `refinement_induction` with `h : a ≤ refinement a`).

---

### `Allegories/TRA/Modalities.lean` (E2)

```
Imports: Allegories.TRA.Basic
Purpose: The □, ♦, ♢ modalities arising from the TRA substitution structure.
```

```lean
/-- The closed-terms modality: `□a = a[⊥]`. -/
def box [TRA A] (a : A) : A := ...  -- substitution applied to ⊥

/-- The open-terms comodality: `♦a = a » ⊥`. -/
def diamond [TRA A] (a : A) : A := ...

/-- The open extension: `♢a = ∆ » ♦a`. -/
def openExt [TRA A] (a : A) : A := comp identity (diamond a)

scoped[TRA] prefix:75 "□" => box
scoped[TRA] prefix:75 "♦" => diamond
scoped[TRA] prefix:75 "♢" => openExt
```

Key laws to prove:
- `box_comp : □(a ⊙ b) = □a ⊙ □b`
- `box_identity_is_bot : □identity = ⊥` (or per the paper: `□∆η = ⊥`)
- `box_idem : □(□a) = □a` (□ is a comonad)
- `box_le : □a ≤ a`
- `galois_box_diamond : □a ≤ b ↔ a ≤ ♦b` (adjunction)

---

### `Allegories/TRA/FixedPointLemmas.lean` (E3)

```
Imports: Allegories.TRA.Basic, Allegories.TRA.Modalities, Mathlib.Order.FixedPoints
Purpose: Lemma 16 — closed monotone functions preserve closedness of fixed points.
```

The key result: if `F` is a `□`-closed monotone function (`□(F x) ≤ F(□x)`) then
`□(OrderHom.lfp F) = OrderHom.lfp (F ∘ box)`.

Use `OrderHom.lfp_induction` from `Mathlib.Order.FixedPoints`.

---

### `Allegories/TRA/Harmony.lean` (H1 — CRITICAL)

```
Imports: Allegories.TRA.Basic, Allegories.TRA.Properties
Purpose: The Harmony axiom — an additional axiom beyond the four TRA conditions.
         NOT derivable from TRA alone; must be declared explicitly and verified on
         every concrete instantiation (especially λ-calculus I6).
```

```lean
/-- The Harmony axiom (Gavazzo Sec. 6.1.1): for any compatible `b`,
    `⟨b̂, b⟩ ⊙ b ≤ b ⊙ b[b]`.
    Computation is parametric: behaviour is fully determined by the outermost
    constructor and its subterms. Required for congruence (Lemma 34, S3). -/
class HarmonicTRA (A : Type*) extends TermRelationAlgebra A where
  harmony : ∀ (b : A), IsCompatible b →
      comp (... ) b ≤ comp b (substitution b b)
```

(The exact statement requires the operational decomposition constructor `⟨·,·⟩` from O1;
declare this file after `Allegories/TRA/Operational/Decomposition.lean` is written,
or add a `harmony` field directly to a combined `OperationalTRA` class.)

---

### `Allegories/TRA/Operational/Decomposition.lean` (O1)

```
Imports: Allegories.TRA.Basic, Allegories.TRA.Modalities
Purpose: Def. 23 — the intro/elim split of the refinement relator.
         Formalizes the CBN vs CBV distinction algebraically.
```

```lean
/-- An operational decomposition of a TRA is a decomposition of the refinement
semirelator into introduction forms (·) and elimination forms (⟨·,·⟩), forming
a cocartesian triple. -/
class OperationalTRA (A : Type*) extends TermRelationAlgebra A where
  /-- Introduction relator: `ã = intro(a)`. -/
  intro_rel   : A → A
  /-- Elimination relator: `⟨a, b⟩`. -/
  elim_rel    : A → A → A

  /-- Refinement decomposes: `ã = intro(a) ⊔ elim(a, ·)`. -/
  refinement_decomp  : ∀ (a : A), refinement a = ...
  /-- Constructors and destructors are disjoint. -/
  intro_elim_disjoint : ∀ (a b c : A), comp (intro_rel a) (elim_rel b c) ≤ ⊥
  /-- □ distributes over elim: `□(⟨a, b⟩) = ⟨□a, b⟩`. -/
  box_elim    : ∀ (a b : A), box (elim_rel a b) = elim_rel (box a) b
  /-- Canonical forms: `∆κ = □∆`. -/
  canonical   : box identity = identity  -- or a dedicated `canonical` element
```

---

### `Allegories/TRA/Operational/GIP.lean` (O2 — CRITICAL)

```
Imports: Allegories.TRA.Operational.Decomposition
Purpose: Def. 24 — Gentzen's Inversion Principle (algebraic form).
         LOCAL CONDITION 1 for Bridge Theorem 37.
```

```lean
/-- Gentzen's Inversion Principle: `a ≤ ⟨∆⟩ ⊙ a`. Computation arises only when an
elimination form has an introduction form as its major argument. -/
def satisfiesGIP [OperationalTRA A] (a : A) : Prop :=
  a ≤ comp (elim_rel identity identity) a
```

Key consequence: `satisfiesGIP_implies_var_irreducible : satisfiesGIP a → comp identity a = ⊥`
(variables are not reducible under GIP reductions).

---

### `Allegories/TRA/Operational/GCP.lean` (O3 — CRITICAL)

```
Imports: Allegories.TRA.Operational.Decomposition, Allegories.TRA.Properties
Purpose: Def. 33 — Gentzen's Conservation Principle.
         LOCAL CONDITION 2 for Bridge Theorem 37. Related to Harmony (H1).
```

```lean
/-- Gentzen's Conservation Principle: for any compatible `x`,
    `⟨x̂, x⟩ ⊙ a ≤ a ⊙ x[x]`.
    Computation is parametric in subterms and proceeds by substitution. -/
def satisfiesGCP [OperationalTRA A] (a : A) : Prop :=
  ∀ (x : A), IsCompatible x →
      comp (elim_rel (refinement x) x) a ≤ comp a (substitution x x)
```

---

### `Allegories/TRA/Reduction/Basic.lean` (R1)

```
Imports: Allegories.TRA.Basic
Purpose: Definition of "reduction" — the nontriviality condition ∆η ; a = ⊥.
```

```lean
/-- `a` is a reduction if variables are not reducible: `∆η ⊙ a = ⊥`. -/
def IsReduction [TRA A] (a : A) : Prop := comp identity a = ⊥
```

---

### `Allegories/TRA/Reduction/ParallelReduction.lean` (R2)

```
Imports: Allegories.TRA.Reduction.Basic, Allegories.TRA.Properties
Purpose: Parallel reduction a⇛ and convertibility a≈.
```

```lean
/-- Parallel reduction: `a⇛ = (∆ ⊔ a[∆])ᴴ`. -/
noncomputable def parallelReduction [TRA A] (a : A) : A :=
  howe (identity ⊔ substitution a identity)

/-- Symmetric-reflexive-transitive closure = convertibility. -/
noncomputable def convertibility [TRA A] (a : A) : A :=
  star (parallelReduction a ⊔ converse (parallelReduction a))

scoped[TRA] postfix:80 "⇛" => parallelReduction
scoped[TRA] postfix:80 "≈ₜ" => convertibility
```

---

### `Allegories/TRA/Reduction/Confluence.lean` (R3–R5)

```
Imports: ..., Mathlib.Order.FixedPoints
Purpose: Abstract confluence, diamond property, Church-Rosser,
         and confluence of orthogonal reductions (Theorem 21).
```

Key definitions:
```lean
def hasDiamondProperty [TRA A] (a : A) : Prop :=
  converse a ⊙ a ≤ a ⊙ converse a

def isConfluent [TRA A] (a : A) : Prop :=
  hasDiamondProperty (star a)

def isChurchRosser [TRA A] (a : A) : Prop :=
  star (a ⊔ converse a) = comp (star a) (converse (star a))
```

Main theorem (Theorem 21 / R5):
```lean
theorem confluent_of_orthogonal [TRA A] {a : A}
    (hreduct : IsReduction a)
    (horth1  : converse (substitution a identity) ⊙ substitution a identity ≤ identity)
    (horth2  : ...)  -- second orthogonality condition
    : isConfluent a
```
Proof follows Gavazzo 2023 using only TRA laws.

---

### `Allegories/TRA/Evaluation/BigStep.lean` (B1–B3)

```
Imports: Allegories.TRA.Operational.*, Allegories.TRA.Reduction.*, Mathlib.Order.FixedPoints
Purpose: One-step evaluation aE, big-step evaluation a⇓, and their inductive characterization.
```

```lean
/-- One-step evaluation: `aE = (a ⊔ ∆)ᶠ` where F is the aF structural recursion. -/
noncomputable def oneStep [OperationalTRA A] (a : A) : A := ...

/-- Big-step evaluation: `a⇓ = aE⋆ ⊙ ∆κ`. -/
noncomputable def bigStep [OperationalTRA A] (a : A) : A :=
  comp (star (oneStep a)) (box identity)

scoped[TRA] postfix:80 "⇓" => bigStep
```

Proposition 29: `a⇓` is the least solution of `x = ∆ ⊔ ⟨x⟩ ⊙ a ⊙ x`.
Use `OrderHom.lfp_le_fixed` from `Mathlib.Order.FixedPoints`.

---

### `Allegories/TRA/Evaluation/Determinism.lean` (B4 — CRITICAL, NEW RESULT)

```
Imports: Allegories.TRA.Evaluation.BigStep, Allegories.TRA.Operational.GIP
Purpose: Theorem 31 — deterministic ground reduction implies deterministic big-step.
```

```lean
/-- Theorem 31 (Gavazzo 2026): if `a` is a closed reduction with `a ⊙ a° ≤ ∆`,
    then `a⇓° ⊙ a⇓ ≤ ∆κ`. -/
theorem bigStep_deterministic [OperationalTRA A] {a : A}
    (hclosed : box a = a)
    (hdet    : comp a (converse a) ≤ identity)
    (hgip    : satisfiesGIP a)
    : comp (converse (bigStep a)) (bigStep a) ≤ box identity
```

---

### `Allegories/TRA/Similarity/Basic.lean` (S1)

```
Imports: Allegories.TRA.Evaluation.BigStep, Mathlib.Order.FixedPoints
Purpose: b-simulation, (open) similarity, bisimilarity via greatest fixed points.
```

```lean
/-- The b-simulation functor: `B(a) = (b⪆ ⊙ a) ← b⪆`. -/
noncomputable def simFunctor [TRA A] (b : A) : A →o A where
  toFun    a := ...   -- right residual
  monotone' := ...

/-- b-similarity: greatest fixed point of the simulation functor. -/
noncomputable def similarity [TRA A] (b : A) : A :=
  (simFunctor b ∘ openExt).gfp  -- uses OrderHom.gfp from Mathlib.Order.FixedPoints

/-- b-bisimilarity. -/
noncomputable def bisimilarity [TRA A] (b : A) : A := ...

scoped[TRA] infixl:50 " ⪆ " => similarity
scoped[TRA] infixl:50 " =∼ " => bisimilarity
```

Use `OrderHom.le_gfp` and `gfp_induction` for coinductive proofs.

---

### `Allegories/TRA/Similarity/HoweExtension.lean` (S2)

```
Imports: Allegories.TRA.Similarity.Basic, Allegories.TRA.Harmony
Purpose: Op-Howe extension a§ = (♢a)ᴴ° and its four key properties.
```

```lean
/-- The op-Howe extension of `a`: `a§ = (♢a)ᴴ°`. -/
noncomputable def opHowe [HarmonicTRA A] (a : A) : A :=
  converse (howe (openExt a))

scoped[TRA] postfix:80 "§" => opHowe
```

Key lemmas (Lemma B.7):
- `opHowe_identity_le : identity ≤ a§`
- `opHowe_comp_le : comp (a§) (a§) ≤ a§`
- `opHowe_compatible : isCompatible (a§)`
- `opHowe_quasi_trans : comp (openExt a) (a§) ≤ a§`

---

### `Allegories/TRA/Bridge.lean` (M1–M2 — MAIN RESULT)

```
Imports: all of TRA/*, Instances not needed here
Purpose: Lemma 36 (GCP+GIP → orthogonality) and Theorem 37 (Bridge Theorem).
```

```lean
/-- Lemma 36: GCP + GIP imply the second orthogonality condition. -/
theorem orthogonality_of_gcp_gip [OperationalTRA A] {a : A}
    (hgip : satisfiesGIP a)
    (hgcp : satisfiesGCP a)
    : comp (converse (substitution a identity))
           (parallelReduction (refinement a) (substitution a identity))
      ≤ comp (converse a) (parallelReduction a)

/-- Theorem 37 — Bridge Theorem (Gavazzo 2026, MAIN RESULT):
    Two local, algebraically checkable conditions imply three fundamental
    metatheorems: confluence, determinism of evaluation, and congruence
    of bisimilarity. -/
theorem bridge_theorem [OperationalTRA A] [HarmonicTRA A] {a : A}
    (hdet  : comp (substitution a identity) (converse (substitution a identity)) ≤ identity)
    (hgip  : satisfiesGIP a)
    (hgcp  : satisfiesGCP a)
    : isConfluent a                                         -- (i)  Confluence
    ∧ comp (converse (bigStep (box a))) (bigStep (box a)) ≤ box identity  -- (ii) Determinism
    ∧ IsSubstitutive (openExt (bisimilarity (box a)))       -- (iii) Congruence
```

---

### `Allegories/Instances/Lambda/Terms.lean` (I2 — CRITICAL)

```
Imports: Mathlib.Data.List.Basic (or similar for variable management)
Purpose: Lambda calculus terms modulo α-equivalence as a concrete TRA.
```

Design decision for binder representation — three options:
1. **de Bruijn indices** (simplest for Lean, no α-equivalence issue): recommended
2. **Nominal sets** (`Mathlib` has partial support)
3. **Fiore-Plotkin-Turi presheaf method**

With de Bruijn:
```lean
inductive LambdaTerm : ℕ → Type where
  | var : Fin n → LambdaTerm n
  | lam : LambdaTerm (n + 1) → LambdaTerm n
  | app : LambdaTerm n → LambdaTerm n → LambdaTerm n
```

A relation on lambda terms in context n is a `Set (LambdaTerm n × LambdaTerm n)`.
The TRA is the `RelationAlgebra` on this type of relations.

Document carefully: the choice of binder representation is a formalization decision
with no canonical answer; justify de Bruijn as the pragmatic choice for Lean 4.

---

### `Allegories/Instances/Lambda/Beta.lean` (I4–I6)

```
Imports: Allegories.Instances.Lambda.Terms, Allegories.Instances.Lambda.Operational
         Allegories.TRA.Operational.GIP, Allegories.TRA.Operational.GCP
         Allegories.TRA.Harmony
Purpose: Verify all three local conditions for β-reduction.
```

Three propositions, each a `theorem` with a paper-reference comment:

1. `beta_reduction_is_reduction` — `IsReduction beta` (variables not β-reducible)
2. `beta_satisfies_gip` — `satisfiesGIP beta` (only redexes `app(lam(−),−)` reduce)
3. `beta_substitution_deterministic` — `comp (substitution beta identity) (converse ...) ≤ identity`
4. `beta_satisfies_gcp` — `satisfiesGCP beta` (most complex; requires Harmony for λ-calculus)

---

### `Allegories/Instances/Lambda/Confluence.lean` (I7 — FINAL COROLLARY)

```
Imports: all of Allegories/Instances/Lambda/*, Allegories.TRA.Bridge
Purpose: Instantiate Bridge Theorem 37 to obtain Church-Rosser, determinism, congruence.
```

```lean
/-- Church-Rosser theorem for the λ-calculus: β⇛ is confluent.
    Obtained as Corollary of Theorem 37 applied to β-reduction. -/
theorem lambda_church_rosser : isConfluent (parallelReduction beta) := by
  exact (bridge_theorem beta_substitution_deterministic beta_satisfies_gip beta_satisfies_gcp).1

/-- Determinism of CBN evaluation for closed λ-terms. -/
theorem lambda_evaluation_deterministic : ... :=
  (bridge_theorem ...).2.1

/-- Applicative bisimilarity is a congruence for the λ-calculus. -/
theorem lambda_bisimilarity_congruence : ... :=
  (bridge_theorem ...).2.2
```

This file is the **payoff** of the entire formalization. It should be short —
all the work is in the abstract framework.

---

## Dependency Ordering for Implementation

Implement files in strict dependency order:

```
Phase 1 (complete existing sorry):
  RelationAlgebra.lean — resolve 6 sorry

Phase 2 (extend allegory layer):
  Maps.lean
  ColaxRelator.lean

Phase 3 (TRA core):
  TRA/Basic.lean
  TRA/Properties.lean
  TRA/Modalities.lean
  TRA/FixedPointLemmas.lean

Phase 4 (operational structure):
  TRA/Operational/Decomposition.lean
  TRA/Operational/GIP.lean
  TRA/Operational/GCP.lean
  TRA/Operational/FOperator.lean
  TRA/Harmony.lean

Phase 5 (reduction theory):
  TRA/Reduction/Basic.lean
  TRA/Reduction/ParallelReduction.lean
  TRA/Reduction/Orthogonality.lean
  TRA/Reduction/Confluence.lean

Phase 6 (evaluation):
  TRA/Evaluation/BigStep.lean
  TRA/Evaluation/Determinism.lean

Phase 7 (similarity):
  TRA/Similarity/Basic.lean
  TRA/Similarity/HoweExtension.lean
  TRA/Similarity/Congruence.lean

Phase 8 (bridge):
  TRA/Bridge.lean

Phase 9 (lambda calculus):
  Instances/Lambda/Terms.lean
  Instances/Lambda/Operational.lean
  Instances/Lambda/Beta.lean
  Instances/Lambda/Confluence.lean
```

---

## `Allegories.lean` Root Index

Update as each phase completes:
```lean
-- Layer 1: Allegory infrastructure
import Allegories.Basic
import Allegories.Lemmas
import Allegories.Structures
import Allegories.Maps
import Allegories.Relator
import Allegories.ColaxRelator
import Allegories.RelationAlgebra
-- Layer 2: TRA
import Allegories.TRA.Basic
import Allegories.TRA.Properties
import Allegories.TRA.Modalities
import Allegories.TRA.FixedPointLemmas
import Allegories.TRA.Harmony
import Allegories.TRA.Operational.Decomposition
import Allegories.TRA.Operational.GIP
import Allegories.TRA.Operational.GCP
import Allegories.TRA.Operational.FOperator
import Allegories.TRA.Reduction.Basic
import Allegories.TRA.Reduction.ParallelReduction
import Allegories.TRA.Reduction.Orthogonality
import Allegories.TRA.Reduction.Confluence
import Allegories.TRA.Evaluation.BigStep
import Allegories.TRA.Evaluation.Determinism
import Allegories.TRA.Similarity.Basic
import Allegories.TRA.Similarity.HoweExtension
import Allegories.TRA.Similarity.Congruence
import Allegories.TRA.Bridge
-- Layer 3: Instances
import Allegories.Instances.Lambda.Terms
import Allegories.Instances.Lambda.Operational
import Allegories.Instances.Lambda.Beta
import Allegories.Instances.Lambda.Confluence
```

---

## Critical Design Decisions to Propagate

1. **`RelationAlgebra` stays standalone** — no dependency on `Allegory`.
   The connection `LocallyCompleteAllegory → RelationAlgebra` is an instance to be
   proved in `TRA/Basic.lean` or a dedicated `Allegories/AllegoryIsRA.lean`.

2. **TRA is also standalone** — `TermRelationAlgebra` extends `RelationAlgebra`,
   not `Allegory`. The representation theorem (every TRA ≅ A(X,X) for some allegory)
   is a theorem, not a definition.

3. **`InitialAlgebra` is custom** — use `Mathlib.CategoryTheory.Monad.Algebra`
   as a base but define `IsInitialAlgebra` as a `Prop` via `IsInitial` from
   `Mathlib.CategoryTheory.Limits.IsLimit` rather than a bundled structure.

4. **Howe extension uses `OrderHom.lfp`** from `Mathlib.Order.FixedPoints` —
   the paper's `µx.x̃⊙a` is exactly `OrderHom.lfp` applied to `fun x => comp (refinement x) a`.
   Monotonicity of this map follows from `refinement_mono` + `comp_mono_left`.

5. **Greatest fixed points for similarity** use `OrderHom.gfp` from the same file.
   Coinductive reasoning goes through `le_gfp` and `gfp_induction`.

6. **De Bruijn indices for λ-calculus** — simplest option for Lean 4, avoids
   nominal-set infrastructure. All binder operations become natural number arithmetic.
   Document this choice explicitly in `Terms.lean`'s module docstring.

7. **`ωCocontinuous` relator** — use `ωScottContinuous` from
   `Mathlib.Order.OmegaCompletePartialOrder`. Each hom-set in a
   `LocallyCompleteAllegory` must be given an `OmegaCompletePartialOrder` instance
   (it already has `CompleteLattice`; use `OmegaCompletePartialOrder.lift` or the
   automatic instance via `CompleteLattice.toOmegaCompletePartialOrder`).
