# LeanTRA

A Lean 4 formalisation of Gavazzo's **Term Relation Algebras** (TRAs) and the
pointfree metatheory of syntax-based systems built on top of them.

This is the software artifact accompanying Jacopo Angeli's master's thesis at
the University of Padua, supervised by Francesco Gavazzo.

## What this is

Semantic notions in programming languages — reduction, evaluation, typing,
program equivalence — are usually specified by syntax-based systems, and their
metatheory (confluence, determinism, congruence of bisimilarity, type safety)
is developed *syntactically*, reproving essentially the same results for every
calculus and every choice of term representation.

Gavazzo's TRAs replace this termwise reasoning with an **algebra of syntax
relations**: metatheorems are stated and proved once, algebraically, with no
reference to any underlying term structure. This project mechanises that
algebra and a first body of its metatheory in Lean 4, on top of Mathlib. In
the code the structure is called `SRA` (Syntax Relation Algebra).

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
├── Algebra/
│   ├── InvolutiveQuantale.lean       -- involutive unital quantale (the base)
│   ├── KleeneStar.lean               -- Kleene star ·∗ and its converse
│   └── Diamond.lean                  -- diamond property, strip lemma, confluence
├── SRA/
│   ├── Basic.lean                    -- the SRA class: Δη, ~·, ·⟦·⟧, j + twenty axioms
│   ├── Howe.lean                     -- Howe extension ·ᴴ, uniqueness, op-Howe ·§
│   ├── Modality.lean                 -- closure modality □/♦, closed relations
│   └── OperationalDecomposition.lean -- intro/elim decomposition, ε(·,·)
├── Metatheory/
│   ├── GentzenPrinciples.lean        -- GIP and GCP
│   ├── Evaluation.lean               -- big-step evaluation fixed points
│   └── Confluence/
│       ├── ParallelReduction.lean    -- parallel reduction a⇛
│       ├── Orthogonal.lean           -- confluence from orthogonality
│       └── Local.lean                -- confluence from the Gentzen principles
│                                        (bridge leg (i))
├── Nominal/
│   └── Basic.lean                    -- nominal sets (for the second-order instance)
└── Instances/
    ├── Toy.lean                      -- two-element consistency model on `Prop`
    ├── FirstOrder/
    │   ├── Terms.lean                -- Signature, Tm, substitution, renaming
    │   ├── Relations.lean            -- SynRel S: lattice/monoid/quantale/involution
    │   ├── SRA.lean                  -- SRA instance + non-degeneracy witnesses
    │   └── Confluence.lean           -- confluent_parRed on the term model
    └── SecondOrder/
        ├── Lambda.lean               -- untyped λ-calculus instance (in progress)
        └── Lambda/
            ├── Syntax.lean           -- λ-syntax as a nominal α-quotient
            └── Substitution.lean     -- capture-avoiding substitution
```

The two typeclasses are `SRA` (`SRA/Basic.lean`) and
`OperationalDecomposition` (`SRA/OperationalDecomposition.lean`, extending the
former); everything else is definitions and theorems over them. The
`Algebra/` layer does not depend on either class and is reusable on its own.

## Status

- [x] Involutive quantale base
- [x] Abstract rewriting (Kleene star, diamond, strip lemma, Church–Rosser)
- [x] SRA axiomatisation and derived laws
- [x] Howe extension with uniqueness of its defining fixed point
- [x] Modality layer (`box`, `dia`, closed relations)
- [x] Operational decomposition and Gentzen principles (GIP/GCP)
- [x] Confluence of parallel reduction, twice: from orthogonality and from the
      Gentzen principles (bridge leg (i))
- [x] Consistency model (`Instances/Toy.lean`) and non-degenerate first-order
      term model (`Instances/FirstOrder/`)
- [ ] Second-order (λ-calculus) instance — in progress, contains `sorry`s
- [ ] Determinism of big-step evaluation (bridge leg (ii))
- [ ] Congruence of applicative bisimilarity (bridge leg (iii))
- [ ] Bridge theorem

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (installed automatically
by `elan`) and the Mathlib version pinned in `lake-manifest.json`.

```sh
lake exe cache get   # fetch prebuilt Mathlib (avoids a very long compile)
lake build
```

The build passes with no `sorry` outside `Instances/SecondOrder/`, whose
remaining gaps are documented in the docstrings of
`Instances/SecondOrder/Lambda.lean` and `Lambda/Substitution.lean`.

## Design conventions

- No `import Mathlib`: files import the specific modules they use.
- The axiom list is kept minimal — laws that are derivable are proved as
  lemmas, not assumed. Each declaration's docstring says whether it is an
  axiom, a definition, or a derived result.
- Consistency of the axiomatisation is checked by an explicit model
  (`Instances/Toy.lean`) and non-degeneracy by the first-order term model
  (`Instances/FirstOrder/`), not assumed.
- Headline theorems carry `#print axioms` commands so their axiom footprint
  is visible in the build log.

## References

- Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
- Francesco Gavazzo. *An Allegorical Account of Term Predicates.* LICS 2023.
