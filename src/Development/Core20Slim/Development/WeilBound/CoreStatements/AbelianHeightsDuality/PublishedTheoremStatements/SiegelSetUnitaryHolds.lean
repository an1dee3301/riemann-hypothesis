module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

namespace PositivityTheory.Prw

theorem siegelCore_holds : PositivityTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Prw
