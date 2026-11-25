module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.Twist := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTwist.twist | exact GlobalTheory.CompanionTheory.RgEisTwist.twist | (intros; apply GlobalTheory.CompanionTheory.RgEisTwist.twist <;> assumption)
