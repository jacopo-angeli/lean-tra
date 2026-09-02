# LeanTRA

A Lean 4 mechanisation of the basic theory of **Term Relation Algebras** (TRAs),
the algebraic framework for the metatheory of syntax-based formal systems
recently introduced by Francesco Gavazzo. This repository is the software
artifact accompanying Jacopo Angeli's master's thesis at the University of
Padua, *Mechanizing Term Relation Algebras: The Basic Theory*, supervised by
Prof. Francesco Gavazzo.

## What the project is about

The semantics of a programming language is rarely given by a single formal
system. Even a small calculus needs an ecosystem of reduction rules, typing
rules, evaluation strategies and notions of program equivalence, and each of
those pieces comes with metatheorems that have to be proved to certify it
behaves as intended. Because those proofs are conducted *termwise*, their steps
mention the specific terms of the calculus and get tied to whatever term
representation happens to be in use, so they must be reproved whenever the
representation changes. Confluence of β-reduction alone has been re-established,
over the decades, for parse trees, for abstract binding trees, for nominal
terms, for de Bruijn indices, and for higher-order abstract syntax, always with
essentially the same argument. A proof that never mentioned a term would not
need to be redone.

TRAs are the algebraic framework that makes such term-free proofs possible.
Formal systems of very different flavours (structural and natural operational
semantics, type theories, rewriting systems, equational theories) admit a
common *provability semantics*: the terms of a concrete calculus are interpreted
into an abstract term structure, and the assertions of the system become
predicates on that structure. Viewed relationally, virtually every term
structure used in program semantics carries the same algebra of predicates, and
this algebra can be axiomatised in a syntax-independent way. This project
mechanises that axiomatisation, together with the first body of its metatheory,
inside Lean 4 on top of Mathlib. In the code the class is called `SRA`
(Syntax Relation Algebra).

The base of the formalisation is a unital involutive quantale rather than a
locally complete allegory. The two are the same algebra of relations written in
different vocabularies at a single object, and the quantale reading is the one
that Mathlib already provides infrastructure for. On top of that base we build
the operators specific to term relation algebras (a variable co-equivalence, a
strict compatible refinement, a substitution operator, a closure constant), the
laws they satisfy, the Howe extension, the modality of closed relations, the
operational decomposition into introduction and elimination forms, and the two
local coherence principles (Gentzen Inversion and Conservation) from which
confluence of parallel reduction follows algebraically.

## Why a proof assistant

A theory of this kind makes two promises that a reader cannot check by
inspection: that its axioms are satisfied by the syntaxes they are meant to
describe, and satisfied non-trivially, so the metatheorems have real content;
and that the metatheorems really do follow from the stated axioms, each step
going through on the assumed structure alone. Both promises are exactly the
kind that a pen-and-paper proof cannot settle on its own, because the phrases
under which gaps hide ("immediate", "by an easy calculation") are precisely the
phrases a reader has to trust. Formalising the development in Lean 4 discharges
both mechanically: nothing is taken on trust beyond the hypotheses actually
written into a statement, and models are exhibited as constructions rather than
claimed.

## Building

The Lean toolchain is pinned in `lean-toolchain` (installed automatically by
`elan`), and the Mathlib version is pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build
```
