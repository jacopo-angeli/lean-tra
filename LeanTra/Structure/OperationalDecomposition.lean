/-!
# Operational decomposition

The extra structure that operational semantics needs on top of a `SRA`: a
splitting of the strict compatible refinement `ẽ·` into an introduction part
`·` and an elimination part `⟨·₁, ·₂⟩`, distinguishing constructors from
destructors and, within destructors, major (eager) from minor (lazy) arguments.

`OperationalDecomposition` extends `SRA`. Determinism and congruence live above
this class; confluence does not need it (it stays at the `SRA` level).

## Axioms (fields of the class)

* `ẽa = intro a ⊔ elim a a` — the two parts recover `ẽ·`.
* `intro` and `elim` weakly unital and orthogonal (constructors and destructors
  disjoint).
* `·[b]` distributes over `intro` and `elim`.
* `□` distributes over `⟨·, b⟩` (major arguments of a closed term are closed).

## Intended contents (definitions, not axioms)

* `⟨a⟩ := elim a Δ`; introduction/elimination co-equivalences; values
  `Δκ := □(intro Δ)`.
* `·ᶠ`, the evaluation recursor (least solution of `x = (Δ ⊔ ⟨x⟩) ; a`).
* one-step evaluation `aᴱ := (a ⊔ Δ)ᶠ` and big-step semantics `a⇓ := aᴱ* ; Δ`.
* `GIP a := a ≤ ⟨Δ⟩ ; a` and `GCP a := ...` as predicates, NOT fields.

## TODO

* [ ] `class OperationalDecomposition extends SRA` with the axiom fields above.
* [ ] `def` for `⟨·⟩`, `Δκ`, `·ᶠ`, `aᴱ`, `a⇓`.
* [ ] `def GIP`, `def GCP`.
* [ ] docstring on every field and definition.

## References

* Francesco Gavazzo. *An Algebraic Approach to Formal System Metatheory.*
  LICS 2026.
-/
