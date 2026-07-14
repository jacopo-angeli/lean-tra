/-!
# Syntax Relation Algebras

A `SRA` is the algebraic structure underlying Gavazzo's Term Relation Algebras,
formalised here over the involutive-quantale base (`IsInvolutiveQuantale`)
rather than over allegories, the two being equivalent in the one-object case.

A `SRA` extends the involutive unital quantale with three data — the variable
co-equivalence `Δη`, the strict compatible refinement `ẽ·` (a weakly unital
morphism), and relation substitution `·[·]` (an oplax bimorphism) — subject to
the axioms recalled below. The derived operation `·̂ := Δη ⊔ ẽ·` (compatible
refinement) is a `def`, not a field.

## Axioms (fields of the class)

* `Δη` is a co-equivalence: symmetric, co-transitive, co-reflexive.
* `ẽ·` weakly unital: monotone, exact on composition and converse, oplax on the
  unit (`ẽ Δ ≤ Δ`).
* `Δη` and `ẽ·` orthogonal (`Δη ; ẽa ≤ ⊥`).
* `Δ` is the least fixed point of `·̂` (fixed-point law + structural induction).
* `·[·]` oplax bimorphism, strict on converse, join-preserving in the first
  argument.
* `(·, Δη, ·[·])` a monoid — recorded as `Prop` fields, NOT as a second `Monoid`
  instance (which would clash with the composition monoid).
* `·[·]` distributes over `ẽ·` (`ẽa[b] ≤ ẽ(a[b])`).

Laws Gavazzo lists but that are derivable — e.g. closedness `·[b] ⊣ b » ·` from
join-preservation — are NOT fields; they are proved in `Derived.lean`.

## TODO

* [ ] `class SRA` with the data and axiom fields above.
* [ ] `def cr` for `·̂ := Δη ⊔ ẽ·`.
* [ ] scoped notation for `Δη`, `ẽ·`, `·[·]`, `·̂`.
* [ ] docstring on every field citing the corresponding axiom.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026. (Presented there over allegories; the involutive-quantale
  presentation used here is equivalent in the one-object case.)
-/
