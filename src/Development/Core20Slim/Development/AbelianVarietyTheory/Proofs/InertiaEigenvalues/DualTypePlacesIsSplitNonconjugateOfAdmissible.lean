module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksPropertiesStatement

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.DualType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.StepLaw (ResAt UnrOff)

variable {D : D7} {S T : HSp D}







section Datum





variable {n r : ℕ}







end Datum

section Source

variable {k R : Type} [CommRing k] [CommRing R] {n r : ℕ}


end Source

section T0

variable {B : Base S T}







end T0

section Scal

variable {B : Base S T}










end Scal

section Main

variable {B : Base S T}



end Main

section Target

variable {B : Base S T}



end Target

section TargetSeries

variable {B : Base S T}

end TargetSeries

section TargetSeriesAll

variable {B : Base S T}



end TargetSeriesAll

section TargetLattice

variable {B : Base S T}

end TargetLattice

section Xi

variable {B : Base S T} {C : Type} [AddCommGroup C] [Fintype C]





end Xi

section Statement

variable {B : Base S T}



end Statement

end GlobalTheory.ExportSeries.DualType

end
