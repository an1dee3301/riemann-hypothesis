module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSetStatement
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

namespace GlobalTheory.CompanionTheory.WTC

theorem weilThetaConvergence_of_core (h : PositivityTheory.ThKR.SiegelCore) : GlobalTheory.Published.WeilThetaConvergence :=
  GlobalTheory.T.theta_convergence_of_siegel_set (PositivityTheory.ThKR.siegel_of_core h)

end GlobalTheory.CompanionTheory.WTC
