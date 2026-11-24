module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearLeftLargeDepth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaContraction_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 0 := by
  first | exact @GlobalTheory.ConnectionLinear.contrLin_left | exact GlobalTheory.ConnectionLinear.contrLin_left | (intros; apply GlobalTheory.ConnectionLinear.contrLin_left <;> assumption)
