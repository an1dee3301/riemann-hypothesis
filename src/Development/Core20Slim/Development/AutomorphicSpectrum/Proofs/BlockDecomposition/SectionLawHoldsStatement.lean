module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_law_holds : PositivityTheory.RgEis.SecLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSec.secLaw | exact GlobalTheory.CompanionTheory.RgEisSec.secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisSec.secLaw <;> assumption)
