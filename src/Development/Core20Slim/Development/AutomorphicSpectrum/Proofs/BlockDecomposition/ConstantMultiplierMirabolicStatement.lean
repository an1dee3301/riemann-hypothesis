module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_multiplier_mirabolic : PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.MirGen → PositivityTheory.RgEis.CMMir := by
  first | exact @GlobalTheory.CompanionTheory.CMMirror.cmMir | exact GlobalTheory.CompanionTheory.CMMirror.cmMir | (intros; apply GlobalTheory.CompanionTheory.CMMirror.cmMir <;> assumption)
