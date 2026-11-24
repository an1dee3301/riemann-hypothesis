module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU

@[expose] public section

open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
