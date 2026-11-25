module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompact
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Prelude
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_detSqrtCover_maxCompact : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  first | exact @GlobalTheory.PolarU.isCompact_Kset | exact GlobalTheory.PolarU.isCompact_Kset | (intros; apply GlobalTheory.PolarU.isCompact_Kset <;> assumption)
