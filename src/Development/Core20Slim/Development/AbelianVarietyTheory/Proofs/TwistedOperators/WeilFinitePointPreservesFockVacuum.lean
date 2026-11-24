module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
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
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
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
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockRealMove

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) {x : GA D V} (hx : x ∈ GfC V) :
    compAt θ τ (mt V x) = 1 :=
  GlobalTheory.LocWeil.CompactPart.infMat_of_fin V (θ τ) hx

theorem om_fin_fockVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x ∈ GfC S, ∀ y ∈ GfC T, IsThetaFunO ψ S T (om (x, y) f) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x, y) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sT f hf hvac x hx y hy
  refine ⟨hW.om_pres _ _ hf, fun τ z => ?_⟩
  have hS : sS τ * compAt θ τ (mt S x) = compAt θ τ (mt S x) * sS τ := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, Matrix.mul_one, Matrix.one_mul]
  have hT : sT τ * compAt θ τ (mt T y) = compAt θ τ (mt T y) * sT τ := by
    rw [compAt_mt_of_mem_GfC θ τ T hy, Matrix.mul_one, Matrix.one_mul]
  have key := GlobalTheory.FockMove.om_annih hW hθ x y τ hS hT (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) hf
  rw [hvac τ, map_zero] at key
  have e : compAt θ τ (mt T y) * (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) * compAt θ τ (mt S x⁻¹) = z := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, compAt_mt_of_mem_GfC θ τ S (inv_mem hx),
      compAt_mt_of_mem_GfC θ τ T hy, compAt_mt_of_mem_GfC θ τ T (inv_mem hy)]
    simp
  rw [e] at key
  exact key.symm

end GlobalTheory.FockRealMove

end
