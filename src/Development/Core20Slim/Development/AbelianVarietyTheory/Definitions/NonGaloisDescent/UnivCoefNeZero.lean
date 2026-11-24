module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct ComplexOrder

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.AdjDatumNe










end GlobalTheory.ExportSeries.Model

end
