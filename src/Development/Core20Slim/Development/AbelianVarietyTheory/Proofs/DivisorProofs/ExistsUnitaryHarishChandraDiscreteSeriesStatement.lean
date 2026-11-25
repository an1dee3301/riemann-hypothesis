module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Prelude

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_harishChandra_discreteSeries : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T), ∃ M : UGKMod p q, M.M = D.HK := by
  first | exact @GlobalTheory.DiscreteSeriesUnitary.exists_unitary | exact GlobalTheory.DiscreteSeriesUnitary.exists_unitary | (intros; apply GlobalTheory.DiscreteSeriesUnitary.exists_unitary <;> assumption)
