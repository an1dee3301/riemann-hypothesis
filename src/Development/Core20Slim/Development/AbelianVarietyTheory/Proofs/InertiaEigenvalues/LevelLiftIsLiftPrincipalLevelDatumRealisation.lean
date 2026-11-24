module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (Vc Wc RealDat Face)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatVecSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType GlobalTheory.ExportType GlobalTheory.ConjTwist

variable {D : D7} {S T : HSp D}
















section Steps

open GlobalTheory.ExportSeries.Model GlobalTheory.AdelicLatMove GlobalTheory.TwoStepModel








end Steps


section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}






end Real


end GlobalTheory.FlatVecSum

end
