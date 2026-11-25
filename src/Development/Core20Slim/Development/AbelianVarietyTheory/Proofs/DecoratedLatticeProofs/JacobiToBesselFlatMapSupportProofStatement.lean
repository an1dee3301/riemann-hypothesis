module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBesselFlatMapSupport_proof : ∀ D : D7, GlobalTheory.FinPl.SupportShift D := by
  first | exact @GlobalTheory.FinPl.supportShift | exact GlobalTheory.FinPl.supportShift | (intros; apply GlobalTheory.FinPl.supportShift <;> assumption)
