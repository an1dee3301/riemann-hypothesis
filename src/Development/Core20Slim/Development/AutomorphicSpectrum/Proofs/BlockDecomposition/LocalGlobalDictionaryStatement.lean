module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  first | exact @GlobalTheory.CompanionTheory.EisDict.dict | exact GlobalTheory.CompanionTheory.EisDict.dict | (intros; apply GlobalTheory.CompanionTheory.EisDict.dict <;> assumption)
