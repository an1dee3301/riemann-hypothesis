module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem theta_annih (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf))

theorem om_annih (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (annih (heisO ψ S T) θ τ (cplxO sS sT) z f) =
      annih (heisO ψ S T) θ τ (cplxO sS' sT') (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  unfold annih
  rw [map_add (f := _), map_smul, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf,
    GlobalTheory.WeilVacMove.cplxO_move θ τ g h hS hT]

theorem om_foldr (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {sS sS' : RealMat S} {sT sT' : RealMat T}
    (hS : ∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ)
    (hT : ∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) :
    IsThetaFunO ψ S T (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) ∧
      om (g, h) (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) =
        (l.map fun p => (p.1, compAt θ p.1 (mt T h) * p.2 * compAt θ p.1 (mt S g⁻¹))).foldr
          (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS' p.1) (sT' p.1)) p.2 F) (om (g, h) f) := by
  induction l with
  | nil => exact ⟨hf, rfl⟩
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ← ih.2]
    exact ⟨theta_annih hθ hW.std p.1 _ p.2 ih.1, om_annih hW hθ g h p.1 (hS p.1) (hT p.1) p.2 ih.1⟩

end GlobalTheory.FockMove

namespace GlobalTheory.FockMove

theorem isFockVec_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (sS sS' : RealMat S) (sT : RealMat T) (g : GA D S), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → ∀ f, IsFockVec ψ θ S T sS sT f → IsFockVec ψ θ S T sS' sT (om (g, 1) f) := by
  intro D ψ S T χS χT om hW θ hθ sS sS' sT g hS f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hT : ∀ τ, sT τ * compAt θ τ (mt T 1) = compAt θ τ (mt T 1) * sT τ := by
    intro τ
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, Matrix.mul_one, Matrix.one_mul]
  refine ⟨hW.om_pres _ _ hth, N, fun l hl => ?_⟩
  let l₀ : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ) :=
    l.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)⁻¹) * p.2 * compAt θ p.1 (mt S g))
  have e : (l₀.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)) * p.2 * compAt θ p.1 (mt S g⁻¹))) = l := by
    simp only [l₀, List.map_map]
    conv_rhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one]
  have key := (om_foldr hW hθ g 1 hS hT hth l₀).2
  rw [e] at key
  rw [← key, hN l₀ (by simp [l₀, hl]), map_zero]

end GlobalTheory.FockMove

end
