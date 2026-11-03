/-
Copyright (c) 2026 Jacopo Angeli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Angeli
-/
import LeanTra

/-!
# Axiom footprint of the main results

Each main result of the library is checked against the axioms it depends on.
A proof that starts using a new axiom (for instance `sorryAx`), or that stops
being choice-free where it was, makes this file fail to build.

Only the three standard axioms `propext`, `Classical.choice` and `Quot.sound`
may appear. The consistency model (`Instances/Consistency.lean`) is
choice-free: its two instances depend on `propext` and `Quot.sound` only.

The expected messages are filled in by Lean: build the file, then use the
code action "Update #guard_msgs" on each command.
-/

/-! ## Algebra -/

/--
info: 'LeanTra.Algebra.IsDiamond.confluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Algebra.IsDiamond.confluent

/-! ## Theory -/

/-- info: 'TRA.box_le_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TRA.box_le_iff

/-- info: 'TRA.box_lfp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TRA.box_lfp

/-! ## Metatheory -/

/--
info: 'LeanTra.Confluence.local_confluence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Confluence.local_confluence

/--
info: 'LeanTra.Confluence.orthogonality_confluence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Confluence.orthogonality_confluence

/--
info: 'LeanTra.Determinism.majorDescent_fixpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Determinism.majorDescent_fixpoint

/--
info: 'LeanTra.Determinism.majorDescent_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Determinism.majorDescent_induction

/--
info: 'LeanTra.Determinism.oneStepEvaluation_fixpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Determinism.oneStepEvaluation_fixpoint

/--
info: 'LeanTra.Determinism.oneStepEvaluation_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Determinism.oneStepEvaluation_induction

/--
info: 'LeanTra.Determinism.bigStep_determinism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Determinism.bigStep_determinism

/-! ## Instances: consistency model -/

/-- info: 'LeanTra.Structure.Model.Toy.instTRA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanTra.Structure.Model.Toy.instTRA

/--
info: 'LeanTra.Structure.Model.Toy.instOperationalDecomposition' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Structure.Model.Toy.instOperationalDecomposition

/-! ## Instances: Peano arithmetic -/

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.instIsInvolutiveQuantale' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.instIsInvolutiveQuantale

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.subst_varDiag_unit_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.subst_varDiag_unit_right

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.scr_compositionality' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.scr_compositionality

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.subst_associativity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.subst_associativity

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.subst_compositionality_oplax' depends on axioms: [propext, Classical.choice]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.subst_compositionality_oplax

/--
info: 'LeanTra.Instances.PeanoArithmetic.instTRA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.instTRA

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.scr_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.scr_decomposition

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.box_elimination_oplaxity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.box_elimination_oplaxity

/--
info: 'LeanTra.Instances.PeanoArithmetic.instOperationalDecomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.instOperationalDecomposition

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_isReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_isReduction

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_isSubstitutiveAtIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_isSubstitutiveAtIdentity

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_isDeterministic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_isDeterministic

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_gip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_gip

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_gcp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_gcp

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_confluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_confluent

/--
info: 'LeanTra.Instances.PeanoArithmetic.TrmRel.rule_bigStep_determinism' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.PeanoArithmetic.TrmRel.rule_bigStep_determinism

/-! ## Instances: untyped λ-calculus -/

/--
info: 'LeanTra.Instances.Lambda.TrmRel.instTRA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.instTRA

/--
info: 'LeanTra.Instances.Lambda.TrmRel.instOperationalDecomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.instOperationalDecomposition

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_isReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_isReduction

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_isSubstitutiveAtIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_isSubstitutiveAtIdentity

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_isDeterministic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_isDeterministic

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_gip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_gip

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_gcp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_gcp

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_local_confluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_local_confluent

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_confluent_orthogonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_confluent_orthogonal

/--
info: 'LeanTra.Instances.Lambda.TrmRel.betaRule_bigStep_determinism' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.betaRule_bigStep_determinism

/--
info: 'LeanTra.Instances.Lambda.TrmRel.not_subst_scr_oplaxity_unguarded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanTra.Instances.Lambda.TrmRel.not_subst_scr_oplaxity_unguarded
