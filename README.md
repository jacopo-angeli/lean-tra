# LeanTRA

A Lean 4 formalisation of Gavazzo's **Term Relation Algebras** (TRAs) and the
pointfree metatheory of syntax-based systems built on top of them.

This is the software artifact accompanying [your name]'s master's thesis at the
University of [...], supervised by [...].

## What this is

Semantic notions in programming languages — reduction, evaluation, typing,
program equivalence — are usually specified by syntax-based systems, and their
metatheory (confluence, determinism, congruence of bisimilarity, type safety)
is developed *syntactically*, reproving essentially the same results for every
calculus and every choice of term representation.

Gavazzo's TRAs replace this termwise reasoning with an **algebra of syntax
relations**: metatheorems are stated and proved once, algebraically, with no
reference to any underlying term structure. This project mechanises that
algebra and a first body of its metatheory in Lean 4, on top of Mathlib.

The base algebra is formalised as a **unital involutive quantale** rather than
as an allegory (the two are equivalent in the one-object case): this rests
directly on Mathlib's `IsQuantale` and avoids categorical overhead.

## Goal

The target result is the **bridge theorem**: from two local coherence
conditions on a ground reduction — Gentzen's Inversion and Conservation
Principles — three metatheorems from three traditionally separate areas follow
at once:

- **confluence** of parallel reduction (rewriting),
- **determinism** of big-step evaluation (operational semantics),
- **congruence** of applicative bisimilarity (program equivalence).

## Structure

```
LeanTra/
├── Basic.lean
├── Structure/
│   ├── InvolutiveQuantale.lean       -- involutive unital quantale (the base)
│   ├── SRA.lean                      -- Syntax Relation Algebra: Δη, tilde ·, ·[·]
│   ├── Derived.lean                  -- derived laws, ·ᴴ, □/♦, cohesion
│   └── OperationalDecomposition.lean -- intro/elim, a⇓, GIP/GCP (stub)
├── Confluence/
│   ├── Abstract.lean                 -- Kleene ·∗, Diamond, Confluent, strip
│   └── Orthogonal.lean               -- parRed, IsOrthogonal, confluent_parRed
└── Instances/
    └── FirstOrder/
        ├── Terms.lean                -- Signature, Tm, substitution, renaming
        ├── Relations.lean            -- SynRel S: lattice/monoid/quantale/involution
        ├── SRA.lean                  -- the sixteen SRA axioms + instSRA + (D-C7)
        └── Confluence.lean           -- confluent_parRed on the term model
```

The two typeclasses are `SRA` and `OperationalDecomposition` (the latter
extends the former); everything else is definitions and theorems over them.

## Status

- [x] Involutive quantale base
- [x] SRA axiomatisation
- [x] Derived laws
- [x] Non-degenerate model
- [x] Confluence
- [ ] Operational decomposition
- [ ] Determinism
- [ ] Congruence
- [ ] Bridge theorem

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (installed automatically
by `elan`) and the Mathlib version pinned in `lake-manifest.json`.

```sh
lake exe cache get   # fetch prebuilt Mathlib (avoids a very long compile)
lake build
```

The build is intended to pass with no warnings and no `sorry`.

## Design conventions

- No `import Mathlib`: files import the specific modules they use.
- The axiom list is kept minimal — laws that are derivable are proved as
  lemmas, not assumed. Each declaration's docstring says whether it is an
  axiom, a definition, or a derived result.
- Consistency of the axiomatisation is checked by an explicit non-degenerate
  model (`Instances/FirstOrder/`), not assumed.

## References

- Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
