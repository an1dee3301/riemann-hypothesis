module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIteratedQuotientIntegralFinsetSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.SphMove

theorem isSphOff_om : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  intro D ψ A B χA χB om hW LA LB hA hB Sf g hg f hf hsph
  have hmv : GlobalTheory.FinPl.Moves A g LA LA (fun v => v ∉ Sf) :=
    (GlobalTheory.QLawPf.moves_iff_forall hA _ g).2 fun v hv =>
      (GlobalTheory.StMoves.moves_iff_stabLoc A LA hA.1.fg v g).2 (hg v hv)
  have hmi : GlobalTheory.FinPl.Moves A g⁻¹ LA LA (fun v => v ∉ Sf) := GlobalTheory.StMoves.moves_inv hmv
  have hm1 : GlobalTheory.FinPl.Moves B (1 : GA D B)⁻¹ LB LB (fun v => v ∉ Sf) := by
    intro y _
    rw [inv_one, show mt B (1 : GA D B) = 1 from rfl, Matrix.one_mulVec]
  have key : ∀ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf),
      actO A B g⁻¹ (1 : GA D B)⁻¹ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf) :=
    fun u hu => GlobalTheory.MidVacLat.actO_mem_latO hA hA hB hB hmi hm1 hu
  have step : ∀ w, heisO ψ A B (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f = f →
      heisO ψ A B w (om (g, 1) f) = om (g, 1) f := by
    intro w hw
    have h := hW.om_heis g 1 (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f hf
    rw [hw, GlobalTheory.MidVacLat.actO_actO_inv] at h
    exact h.symm
  refine ⟨fun u hu => step _ ?_, fun e he u hu hh => step _ ?_⟩
  · rw [GlobalTheory.MidVacLat.actO_two_nsmul]
    exact hsph.1 _ (key u hu)
  · exact hsph.2 e he _ (key u hu) (GlobalTheory.MidVacLat.isHalf_actO _ _ hh)

end GlobalTheory.SphMove
