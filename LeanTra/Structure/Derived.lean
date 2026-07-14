/-!
# Derived laws of Syntax Relation Algebras

Consequences of the `SRA` axioms: the "small contributions" — laws Gavazzo
states as axioms but that follow from a smaller set — together with the derived
operations used throughout the metatheory.

Nothing here is an axiom; every declaration is a theorem or a definition over
`SRA`. This file is the first real test of the axiomatisation: if a law below
fails to derive, the axiom list in `SRA.lean` is either too weak or wrong.

## Intended contents

* Basic laws of `·̂`, `ẽ·`, and substitution (compatibility, converse,
  distributivity), including `ẽ Δ ≤ Δ` and the interaction laws.
* Closedness of substitution `·[b] ⊣ b » ·`, derived from join-preservation in
  the first argument via the posetal Adjoint Functor Theorem.
* The Howe extension `·ᴴ` as a least fixed point, with its fixed-point law,
  induction principle, and uniqueness.
* Relation substitution as a `def`, with its monoid laws already available from
  `SRA`.
* The modalities `□a := a[⊥]` and `♦a := a » ⊥`, closed relations, and the
  cohesion laws relating them.

## TODO

* [ ] compatible/strict-refinement laws.
* [ ] `·[b] ⊣ b » ·` closedness.
* [ ] `def howe` (`·ᴴ`) + fixed-point law + induction + uniqueness.
* [ ] `def box`, `def dia`, closed-relation predicate, cohesion laws.
* [ ] mark reusable equalities `@[simp]` where appropriate.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
