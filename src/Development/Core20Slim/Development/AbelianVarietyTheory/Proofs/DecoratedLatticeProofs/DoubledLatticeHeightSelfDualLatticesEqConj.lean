module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdelicConjSelfDualDoublingCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem hgtL_eq_conj_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ g, hgtL A L' a g = hgtL A L a (k⁻¹ * g * k) := by
  intro D A L L' hL hL'
  obtain ⟨k, hk, hK⟩ := GlobalTheory.T.exists_finiteAdelic_conj_selfDual_doublingCompact D A L L' hL hL'
  refine ⟨k, hk, fun a ha g => ?_⟩
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L hL
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L' hL'
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L' a hL' ha
  have hj : io A (k, k) ∈ siegel A := (io_mem_siegel A).2 rfl
  obtain ⟨p, κ, hκ, hx⟩ := hI (io A (g, 1))
  have hκ' : (io A (k, k))⁻¹ * κ * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := (hK a κ).1 hκ
  have e : io A (k⁻¹ * g * k, 1) =
      ((⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) : GA D (dblSp A)) *
        ((io A (k, k))⁻¹ * κ * io A (k, k)) := by
    have h1 : io A (k⁻¹ * g * k, 1) = (io A (k, k))⁻¹ * io A (g, 1) * io A (k, k) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      simp
    rw [h1, hx]
    simp [mul_assoc]
  change hgtAd _ _ L' a (io A (g, 1)) = hgtAd _ _ L a (io A (k⁻¹ * g * k, 1))
  rw [hx, e]
  calc
    hgtAd _ _ L' a (↑p * κ) = _ := hgtAd_mul (isCMExt_host D) p hκ
    _ = _ := by
      congr 1
      rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    _ = hgtAd _ _ L a (↑(⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) *
        ((io A (k, k))⁻¹ * κ * io A (k, k))) :=
      (hgtAd_mul (isCMExt_host D) _ hκ').symm

end GlobalTheory.Core.Rk.IP
