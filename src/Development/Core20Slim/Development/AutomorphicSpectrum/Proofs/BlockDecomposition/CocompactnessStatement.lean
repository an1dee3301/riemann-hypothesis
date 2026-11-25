module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompactness : CoCpt := by
  first | exact @GlobalTheory.CompanionTheory.MassCocompact.coCpt | exact GlobalTheory.CompanionTheory.MassCocompact.coCpt | (intros; apply GlobalTheory.CompanionTheory.MassCocompact.coCpt <;> assumption)
