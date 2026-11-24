module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThree
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_three : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  first | exact @GlobalTheory.CompanionTheory.GunrResCard.q3 | exact GlobalTheory.CompanionTheory.GunrResCard.q3 | (intros; apply GlobalTheory.CompanionTheory.GunrResCard.q3 <;> assumption)
