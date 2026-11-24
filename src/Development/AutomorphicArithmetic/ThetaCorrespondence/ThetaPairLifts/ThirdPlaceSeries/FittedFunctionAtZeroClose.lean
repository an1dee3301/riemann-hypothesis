module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareTopTermJoinedEstimates
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeFiniteAwayArchimedeanCombined
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JoinedLocalSumEstimates
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedConvergenceWithRealPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSizeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogDerivLFunctionAtOneLeAlongFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThmAUpperStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareRatioAtPointOfLeadingTerm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleOfRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIntegralMultipleHoldsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaimsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormulaStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafFixedPointOfFinKAwayKStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpbOfLamLowStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneSqTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DenTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ArchTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThbTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesHLeaf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsFifthBoundStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsSeventhBoundStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesPolStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.Close
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem fittedFunction_at_zero_close_alt : FunPr.ThetaLocalInputs → Published.HeckeFunctionalEquationAbs → IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → ToricTransport.TwistedTransport → IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → SqTop.Refl →
    IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate →
    LambdaLowerBound₂ → ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := by
  intro hP hH hTD hTr hTw hZ hR hAg hMa hFS hL
  obtain ⟨hDenSum, hThbSt, hOneSqSt, hBotSmall, hBotNe, hFieldDat, hTorEx, hDenEx, hBotEx, hLNe, hTriEx, hTower⟩ :=
    T.square_leading_term_bound hP.howeDualityReal hP hH hTD hTr hZ hR hAg hMa
  obtain ⟨hFin, hAway, hInf⟩ := T.sum_size_bound_all_places hP
  obtain ⟨hSumOK, hConst, hLin, hF2, hSumRat⟩ := T.local_sum_estimates_joined hP hAg hMa
  have hInj := RowTest.injK_of_separates hFS (RowTest.twisted_convergence_with_real_places hP (T.twisted_thetaLift_cuspidal hP))
  have hSize := T.size_at'
  have hSet := T.set_at_of_size_at' hSize
  have hDl := T.abs_logDerivativeAtOne_le_x_rpow_eps hP
  have hInp := T.cmThetaNormBoundHypotheses_satisfied
  have hIntSt := T.classSumDenominatorBound_of_cmThetaHypotheses hInp
  have hArchSt := ArchTop.archSt_of_inp hInp
  have hThA := T.toric_ratio_family_estimate' (ToricTransport.toricRatioConjugates_of_transport hTw) hSet hDl hFieldDat hTorEx
  have hSq := T.sq_ratio_mem_range_emb_ll hP hAg hMa hSet hDl hConst hLNe hTriEx hTower
  have hB : BundleCondition := @bundle_of_rows_alt
  exact fun0Fit_of_leaves_alt _ _ hB T.scaling_function_bound'
    (T.existsFunctionIn_of_sqRatio_range hSet hDl hSumOK hSumRat hConst hSq hIntSt hFieldDat hTorEx hDenEx hBotEx hBotSmall)
    (T.leafMinimalMass_of_setAt hSet) (T.oneMap_of_bundle_setAt_lin_inj_const_formula hB hSet hLin hInj hConst hF2) (T.leafKernel_tie_of_claim_inputs hB hSet hLin hInj hConst hF2)
    (T.leafFixedPoint_of_finK_awayK hSet hFin hAway) (T.leafHeightMapBound_of_infK hB hSet hInf) (T.leafInfinitePlaceBound_of_lamLow hL)
    (T.oneSq_of_log_derivative_bound_and_oneSqSt hSet hDl hThA hOneSqSt) (T.leafDensity_of_logDeriv_bound_and_denSum hSet hDl hDenSum) (T.leafIntegrality_of_logDeriv_bound hSet hDl hBotSmall hBotNe)
    (T.arch_tie_of_setAt_logDeriv hSet hDl hArchSt hBotSmall) (T.leaf_theta_bound_of_set_at hSet hDl hThbSt) (T.weight_of_size_bound' hSize)
    desHLeaf_alt T.rank_gap_bound T.ramified_sum_bound' T.polynomial_descent_estimate'
end GlobalTheory.BigTop.Fun.Close
end
end
end
