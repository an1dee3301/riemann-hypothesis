module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section
open Classical
set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.IdeleAA

open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)

variable {D : D7}










theorem tmul_eq (p : AF D.host.F) (e : D.host.E) :
    p ⊗ₜ[D.host.F] e = algebraMap (AF D.host.F) (AE D) p * incA D e := by
  change _ = (p ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
variable {D : D7}









end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
variable {D : D7}







end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
open GlobalTheory.FinPl.Conductor (chi chi_add chi_zero psiE_eq_chi approx tmul_mem mul_mem_int lift_mem chi_rat chi_int ev_same ev_ne)
variable {D : D7}










end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
open GlobalTheory.SelfDualAt (cP indP evalV_indP algebraMap_placeIdempotent_mul cA_alg)
open GlobalTheory.FinPl.Conductor (chi chi_add chi_zero psiE_eq_chi approx tmul_mem mul_mem_int lift_mem chi_rat chi_int ev_same ev_ne)
variable {D : D7}
















end GlobalTheory.IdeleAA

namespace GlobalTheory.IdeleAA
variable {D : D7}


end GlobalTheory.IdeleAA

end
