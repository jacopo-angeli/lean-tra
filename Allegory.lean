-- Layer 1 — Allegorie
import Allegory.Basic
import Allegory.Distributive
import Allegory.Division
import Allegory.LocallyComplete

-- Layer 1 — Relator
import Allegory.Relator.Basic
import Allegory.Relator.Cocartesian

-- Layer 2 — TRA core
import Allegory.TRA.Basic
import Allegory.TRA.Properties
import Allegory.TRA.Modalities
import Allegory.TRA.FixedPointLemmas
import Allegory.TRA.Harmony

-- Layer 4 — Decomposizione operazionale
import Allegory.TRA.Operational.Decomposition
import Allegory.TRA.Operational.FOperator
import Allegory.TRA.Operational.GIP
import Allegory.TRA.Operational.GCP

-- Layer 5 — Riduzione
import Allegory.TRA.Reduction.Basic
import Allegory.TRA.Reduction.Confluence
import Allegory.TRA.Reduction.Orthogonality
import Allegory.TRA.Reduction.Parallel
import Allegory.TRA.Reduction

-- Layer 6 — Valutazione
import Allegory.TRA.Evaluation.OneStep
import Allegory.TRA.Evaluation.BigStep
import Allegory.TRA.Evaluation.Proposition29
import Allegory.TRA.Evaluation.Determinism

-- Layer 7 — Similarity
import Allegory.TRA.Similarity.Basic
import Allegory.TRA.Similarity.HoweExtension
import Allegory.TRA.Similarity.Congruence
import Allegory.TRA.Similarity.Theorem35

-- Layer 8 — Bridge Theorem
import Allegory.TRA.Bridge.Lemma36
import Allegory.TRA.Bridge

-- Notation (paper-style aliases; optional, scoped)
import Allegory.Notation

-- Layer 9 — Istanze (placeholder)
import Allegory.Instances.FirstOrder.TRA
import Allegory.Instances.Lambda.Terms
import Allegory.Instances.Lambda.Operational
import Allegory.Instances.Lambda.Beta
import Allegory.Instances.Lambda.Confluence

/-!
# Allegory — Root index

Importa tutti i moduli pubblici della libreria. Tenere allineato con la
struttura di `Allegory/`. L'ordine segue il dependency-DAG dal basso verso
l'alto (allegorie → relator → TRA → operazionale → riduzione → valutazione
→ similarity → bridge → istanze).
-/
