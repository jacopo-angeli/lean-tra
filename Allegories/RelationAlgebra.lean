import Mathlib.Order.BoundedOrder.Lattice

/-!
# Relation algebras

Defines relation algebras in the sense of Ferro, §4.2, Definizione 4.2.1.
A relation algebra is a bounded lattice equipped with a sequential composition monoid,
a converse involution, left and right residuals, and a Kleene star.

This structure is standalone — it does not depend on the allegory hierarchy.

## Main definitions

* `RelationAlgebra` — the main typeclass, extending `Lattice` and `BoundedOrder`
* `RelationAlgebra.converse_identity` — converse of the identity is the identity
* `RelationAlgebra.converse_comp` — converse reverses the order of composition
* `RelationAlgebra.converse_sup` — converse distributes over join
* `RelationAlgebra.comp_mono_left`, `comp_mono_right` — composition is monotone
* `RelationAlgebra.identity_le_star` — the identity is below any star element

## References

* Ferro, *Formalizzazione delle Allegorie*, Università di Padova, 2024/2025, §4.2,
  Definizione 4.2.1
-/

/-- A relation algebra is a bounded lattice `(A, ⊔, ⊓, ⊥, ⊤)` equipped with:
- a monoid `(A, ⊙, δ)` for sequential composition,
- a converse involution `(−)°` satisfying the Galois law `a ≤ b° ↔ a° ≤ b`,
- left and right residuals `⊸` and `⊷` satisfying adjunction conditions,
- a Kleene star `(−)⋆` satisfying unfolding and left induction.

Reference: Ferro, Definizione 4.2.1. -/
class RelationAlgebra (A : Type*) extends Lattice A, BoundedOrder A where
  /-- Sequential composition. -/
  comp : A → A → A
  /-- The identity element (the diagonal, or identity relation). -/
  identity : A
  /-- The converse involution `(−)°`. -/
  converse : A → A
  /-- Left residual: `a ⊸ c` is the largest element `x` with `a ⊙ x ≤ c`. -/
  left_residual : A → A → A
  /-- Right residual: `c ⊷ b` is the largest element `x` with `x ⊙ b ≤ c`. -/
  right_residual : A → A → A
  /-- Kleene star `(−)⋆`. -/
  star : A → A

  /-- Composition is associative. -/
  comp_assoc : ∀ (a b c : A), comp (comp a b) c = comp a (comp b c)
  /-- The identity is a left unit for composition. -/
  identity_comp : ∀ (a : A), comp identity a = a
  /-- The identity is a right unit for composition. -/
  comp_identity : ∀ (a : A), comp a identity = a
  /-- Composition distributes over join on the right. -/
  comp_sup_right : ∀ (a b c : A), comp a (b ⊔ c) = comp a b ⊔ comp a c
  /-- Composition distributes over join on the left. -/
  comp_sup_left : ∀ (a b c : A), comp (a ⊔ b) c = comp a c ⊔ comp b c
  /-- Bottom absorbs composition on the right. -/
  comp_bot : ∀ (a : A), comp a ⊥ = ⊥
  /-- Bottom absorbs composition on the left. -/
  bot_comp : ∀ (a : A), comp ⊥ a = ⊥
  /-- Converse is an involution: `(a°)° = a`. -/
  converse_involution : ∀ (a : A), converse (converse a) = a
  /-- The Galois law for converse: `a ≤ b° ↔ a° ≤ b`. -/
  galois_law : ∀ (a b : A), a ≤ converse b ↔ converse a ≤ b
  /-- Left residual adjunction: `a ⊙ b ≤ c ↔ b ≤ a ⊸ c`. -/
  left_residual_adjunction : ∀ (a b c : A), comp a b ≤ c ↔ b ≤ left_residual a c
  /-- Right residual adjunction: `a ⊙ b ≤ c ↔ a ≤ c ⊷ b`. -/
  right_residual_adjunction : ∀ (a b c : A), comp a b ≤ c ↔ a ≤ right_residual c b
  /-- Star unfolding: `δ ⊔ a ⊙ a⋆ = a⋆`. -/
  star_unfold : ∀ (a : A), identity ⊔ comp a (star a) = star a
  /-- Star left induction: `δ ⊔ a ⊙ b ≤ b → a⋆ ≤ b`. -/
  star_induction_left : ∀ (a b : A), identity ⊔ comp a b ≤ b → star a ≤ b

attribute [simp] RelationAlgebra.identity_comp
attribute [simp] RelationAlgebra.comp_identity
attribute [simp] RelationAlgebra.converse_involution
attribute [simp] RelationAlgebra.comp_bot
attribute [simp] RelationAlgebra.bot_comp

/-- Notation for sequential composition in a relation algebra. -/
scoped[RelationAlgebra] infixl:70 " ⊙ " => RelationAlgebra.comp
/-- Notation for the converse involution in a relation algebra. -/
scoped[RelationAlgebra] postfix:90 "°" => RelationAlgebra.converse
/-- Notation for the left residual in a relation algebra: `a ⊸ c` satisfies
`a ⊙ b ≤ c ↔ b ≤ a ⊸ c`. -/
scoped[RelationAlgebra] infixr:55 " ⊸ " => RelationAlgebra.left_residual
/-- Notation for the right residual in a relation algebra: `c ⊷ b` satisfies
`a ⊙ b ≤ c ↔ a ≤ c ⊷ b`. -/
scoped[RelationAlgebra] infixl:55 " ⊷ " => RelationAlgebra.right_residual
/-- Notation for the Kleene star in a relation algebra. -/
scoped[RelationAlgebra] postfix:90 "⋆" => RelationAlgebra.star

namespace RelationAlgebra

open RelationAlgebra

variable {A : Type*} [RelationAlgebra A]

/-- Converse of the identity is the identity. -/
theorem converse_identity : converse (identity : A) = identity := by
  apply le_antisymm
  · have h1 := galois_law (identity : A) (converse (identity : A))
    simp only [converse_involution] at h1
    exact h1
  · sorry

  -- · -- ∆° ≤ ∆
  --   -- galois_law con a := ∆°, b := ∆:
  --   -- ∆° ≤ ∆° ↔ ∆°° ≤ ∆
  --   rw [show converse (identity : A) =
  --       converse (converse (converse identity)) from by simp]
  --   rw [galois_law]
  --   simp
  -- · -- ∆ ≤ ∆°
  --   rw [galois_law]
  --   simp
/-- Converse reverses the order of composition: `(a ⊙ b)° = b° ⊙ a°`. -/
theorem converse_comp (a b : A) : converse (comp a b) = comp (converse b) (converse a) := by sorry

/-- Converse distributes over join: `(a ⊔ b)° = a° ⊔ b°`. -/
theorem converse_sup (a b : A) : converse (a ⊔ b) = converse a ⊔ converse b := by sorry

/-- Composition is monotone in the left argument. -/
theorem comp_mono_left {a b : A} (c : A) (h : a ≤ b) : comp a c ≤ comp b c := by sorry

/-- Composition is monotone in the right argument. -/
theorem comp_mono_right (a : A) {b c : A} (h : b ≤ c) : comp a b ≤ comp a c := by sorry

/-- The identity is below any Kleene star: `δ ≤ a⋆`. -/
theorem identity_le_star (a : A) : identity ≤ star a := by
  have h := star_unfold a
  rw [← h]
  exact le_sup_left

/-- The star of the identity is the identity: `δ⋆ = δ`. -/
theorem star_identity : star (identity : A) = identity := by sorry

/-- A star element is idempotent under composition: `a⋆ ⊙ a⋆ ≤ a⋆`. -/
theorem star_comp_star_le (a : A) : comp (star a) (star a) ≤ star a := by sorry

end RelationAlgebra
