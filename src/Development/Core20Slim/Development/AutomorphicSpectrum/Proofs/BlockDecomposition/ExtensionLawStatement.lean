module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_law : PositivityTheory.RgEis.ExtLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisExt.extLaw | exact GlobalTheory.CompanionTheory.RgEisExt.extLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisExt.extLaw <;> assumption)
