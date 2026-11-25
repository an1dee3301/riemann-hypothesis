module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_formula_polynomial_gen : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | exact GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly <;> assumption)
