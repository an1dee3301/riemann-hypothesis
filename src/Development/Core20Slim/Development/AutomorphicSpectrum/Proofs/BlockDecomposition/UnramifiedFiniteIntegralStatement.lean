module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_finite_integral : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.finInt | exact GlobalTheory.CompanionTheory.Gunr.finInt | (intros; apply GlobalTheory.CompanionTheory.Gunr.finInt <;> assumption)
