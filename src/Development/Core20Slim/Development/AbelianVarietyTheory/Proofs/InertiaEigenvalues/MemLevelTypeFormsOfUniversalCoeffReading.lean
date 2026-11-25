module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF Vc Wc)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType

variable {D : D7} {S T : HSp D}

section Series



variable {B : Base S T}











end Series

section Algebra

variable {R K A V ι : Type} [CommRing R] [Field K] [Algebra R K] [CommRing A] [Algebra R A] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]


variable {Δ : Type}





end Algebra

section Record

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK UnrG Fm0 ExpDat)

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} {hρ : ρ.Good}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b}











variable (Z : CellTie hρ Y rd) (hA : ActRead rd)
include Z hA





omit Z hA



variable {rds : Rds Y ρ} (W : Comparison₂ hρ rds) (hW : ∀ i j b, ActRead (rds i j b))
include W hW




end Record

section Export

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (Fm0 ExpDat)

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T₀ : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T₀ D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {Sr : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG Sr}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}


end Export

section Target

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie


end Target

end GlobalTheory.ExportType

end
