module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_invariance : AvgMem → AvgInv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | exact GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | (intros; apply GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem <;> assumption)
