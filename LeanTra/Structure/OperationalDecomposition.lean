/-!
# Operational decomposition

Docstring-only stub. Nothing is defined or proved in this file yet; it
records the intended shape of the extension of `SRA` needed for operational
semantics.

The plan is to layer on top of a `SRA` a splitting of the strict compatible
refinement `tilde ·` into an *introduction* part `·` and an *elimination* part
`⟨·, ·⟩`, distinguishing constructors from destructors and, within
destructors, major (eager) from minor (lazy) arguments. Determinism and
congruence will live above this class; confluence will not, staying at the
`SRA` level.

## Planned class

`OperationalDecomposition` will extend `SRA` with:

* an intro/elim split recovering `tilde ·`, i.e. `tilde a = intro a ⊔ elim a a`;
* weak unitality and mutual orthogonality of `intro` and `elim`
  (constructors and destructors disjoint);
* distributivity of `·[b]` over `intro` and `elim`;
* distributivity of `□` over the major-argument slot `⟨·, b⟩` (major
  arguments of a closed term are closed).

## Planned definitions (not fields)

* `⟨a⟩ := elim a Δ`; the introduction/elimination co-equivalences; values
  `Δκ := □(intro Δ)`.
* `·ᶠ`, the evaluation recursor as the least solution of
  `x = (Δ ⊔ ⟨x⟩) ; a`.
* one-step evaluation `aᴱ := (a ⊔ Δ)ᶠ` and big-step semantics
  `a⇓ := aᴱ* ; Δ`.
* Predicates `GIP a := a ≤ ⟨Δ⟩ ; a` and `GCP a := ...`, NOT fields.

## TODO

* [ ] `class OperationalDecomposition extends SRA` with the axiom fields above.
* [ ] `def` for `⟨·⟩`, `Δκ`, `·ᶠ`, `aᴱ`, `a⇓`.
* [ ] `def GIP`, `def GCP`.
* [ ] docstring on every field and definition.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
