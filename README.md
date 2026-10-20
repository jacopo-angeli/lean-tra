# LeanTRA

A Lean 4 mechanisation of the basic theory of **Term Relation Algebras** (TRAs), the algebraic framework for the metatheory of syntax-based formal systems recently introduced by Francesco Gavazzo.

## The idea

The semantics of a programming language is rarely given by a single formal system. Even a small calculus needs an ecosystem of reduction rules, typing rules, evaluation strategies and notions of program equivalence, and each of those pieces comes with metatheorems that have to be proved to certify it behaves as intended. Because those proofs are conducted *termwise*, their steps mention the specific terms of the calculus and get tied to whatever term representation happens to be in use, so they must be reproved whenever the representation changes. Confluence of β-reduction alone has been re-established, over the decades, for parse trees, for abstract binding trees, for nominal terms, for de Bruijn indices, and for higher-order abstract syntax, always with essentially the same argument. A proof that never mentioned a term would not need to be redone.

TRAs are the algebraic framework that makes such term-free proofs possible. Formal systems of very different flavours (structural and natural operational semantics, type theories, rewriting systems, equational theories) admit a common *provability semantics*: the terms of a concrete calculus are interpreted into an abstract term structure, and the assertions of the system become predicates on that structure. Viewed relationally, virtually every term structure used in program semantics carries the same algebra of predicates, and this algebra can be axiomatised in a syntax-independent way. This project mechanises that axiomatisation, together with the first body of its metatheory, inside Lean 4 on top of Mathlib. In the code the class is called `TRA` (Term Relation Algebra).

## Proved so far

The main results so far concern confluence and determinism. In `Metatheory/`, confluence of parallel reduction is derived in two ways: from five conditions that can be checked on a rewrite rule by inspection (among them Gentzen's inversion and conservation principles), and from orthogonality. Determinism of big-step evaluation follows from the same principles. In `Instances/`, these abstract theorems are applied to Peano arithmetic and to the untyped λ-calculus, giving confluence of β-reduction as an instance, while a trivial model shows that the axioms are consistent.

Every file opens with a docstring explaining what it contains and why; `TRA/Basic.lean` also describes how the formalisation relates to the original definition of Term Relation Algebras. Nothing relies on `sorry` or on axioms beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).

## Building

```sh
lake exe cache get   # download a prebuilt Mathlib
lake build
```

The Lean toolchain is pinned in `lean-toolchain` and the Mathlib version in `lake-manifest.json`.

To use LeanTRA in your own Lake project, add it as a dependency in `lakefile.toml`:

```toml
[[require]]
name = "lean-tra"
git = "https://github.com/jacopo-angeli/lean-tra"
rev = "trunk"
```

and `import LeanTra` in your files. Since the library is still evolving,
pinning `rev` to a tag or commit is recommended.

## Contributing

Questions, bug reports and suggestions are welcome as GitHub issues.

## Origin and citation

Term Relation Algebras originate in the work of Francesco Gavazzo. The relational approach to symbolic manipulation was introduced in *Allegories of Symbolic Manipulations* (LICS 2023), and then developed into the algebraic framework for the metatheory of formal systems of *An Algebraic Approach to Formal System Metatheory* (LICS 2026).

LeanTRA started as the software part of the master's thesis *Mechanizing Term Relation Algebras: The Basic Theory* (Jacopo Angeli, University of Padua, 2026), supervised by Prof. Francesco Gavazzo.

## License

Released under the [Apache 2.0 license](LICENSE).