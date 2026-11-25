module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExpansionZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFiniteStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProofStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunctionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasuresStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepthStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypothesesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosetsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedIterateEventuallyLarge
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

section
open GlobalTheory.RowClaim GlobalTheory.RowVal GlobalTheory.RowReal
namespace GlobalTheory.RowUnfLast
theorem twisted_theta_integral_unfolding : FunPr.ThetaLocalInputs → IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := fun p c s =>
  have rel := T.lastRow_real_iterated_integral_eq_const_mul_finite
  have hcv := T.cellSumRelationsPassToIntegrals_proof
  have grp := T.rowPeriodGroups_split_real_finite_large_depth
  have it := T.twisted_iterate_chain
  have inv := T.unfolded_integrand_biInvariant_large_depth
  have flat := RowFlatAsm.flatAt_big
  have supp := T.integrand_supported_on_cells_largeDepth
  have rep := T.representation_at_every_place
  have val := T.rowTest_cellValue_of_steps_large_depth
  have off := T.singleCosetOffTwistPlaces_largeDepth
  have tens := T.definitePeriod_depends_on_productFunction
  have vol := T.rowTest_definitePeriod_change_of_measures
  have wt := T.cell_masses_against_level_volumes_large_depth
  have fock := T.periodReductionToFockVectors_large_depth
  have bas := T.lastRow_unfolding_basicHypotheses
  have one := T.rowTest_support_families_staircase_cosets
  have rl := RowReal.realLine
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rel, grp⟩, it⟩, inv⟩, ⟨e, fl⟩⟩, supp⟩, rep⟩, val⟩, off⟩, tens⟩, vol⟩, wt⟩, fock⟩, bas⟩, one⟩, rl⟩, s⟩ =>
    rel grp it.1 it.2 inv ⟨e, supp e fl off inv tens bas, rep e, val e fl tens vol (wt e) fock bas one s⟩ rl s)
  (((((((((((((((((rel hcv).and grp).and (it p c)).and inv).and flat).and supp).and rep).and val).and off).and tens).and vol).and wt).and fock).and bas).and one).and rl).and s)
end GlobalTheory.RowUnfLast
end

section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_unfolds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := by
  first | exact @_root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding | exact _root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding | (intros; apply _root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding <;> assumption)
end
