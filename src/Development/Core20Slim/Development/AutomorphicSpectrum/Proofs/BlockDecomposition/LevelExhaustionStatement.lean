module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_exhaustion : PositivityTheory.SiegelWeilFormula.Gunr.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)
