module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU

@[expose] public section

open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_iwasawa_estimate : EIwa := by
  first | exact @GlobalTheory.CompanionTheory.SwEisIwa.eIwa | exact GlobalTheory.CompanionTheory.SwEisIwa.eIwa | (intros; apply GlobalTheory.CompanionTheory.SwEisIwa.eIwa <;> assumption)
