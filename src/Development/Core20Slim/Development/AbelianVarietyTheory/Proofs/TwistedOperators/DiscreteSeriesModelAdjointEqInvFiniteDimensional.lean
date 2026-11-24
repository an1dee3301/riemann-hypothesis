module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

namespace GlobalTheory.RepAdj

theorem rep_adjoint_eq_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  intro D V S M τ _ g hg
  have hfd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ))
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ |>.mul (M.fr_unit τ)
  have hgi : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := GlobalTheory.SmVec.inv_mem_UH hG hg
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
  refine ⟨hgi, ?_⟩
  have hU := (M.ds τ).2.2.1
  have m1 : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg
  have m2 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hgi
  have hprod : (M.fr τ * g⁻¹ * (M.fr τ)⁻¹) * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hfd]
    rw [← Matrix.mul_assoc g⁻¹ g, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hfd]
  have hcomp : ∀ x, M.rep τ g⁻¹ (M.rep τ g x) = x := by
    intro x
    have := hU.1.2 _ m2 _ m1
    rw [hprod, hU.1.1] at this
    have hx := congrArg (fun T : M.H τ →L[ℂ] M.H τ => T x) this
    simpa [DSModel.rep] using hx.symm
  have hiso : ∀ x y, inner ℂ (M.rep τ g⁻¹ x) (M.rep τ g⁻¹ y) = inner ℂ x y := by
    have hn : ∀ v, ‖(M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) v‖ = ‖v‖ := fun v => hU.2.1 _ m2 v
    intro x y
    exact (LinearMap.norm_map_iff_inner_map_map (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ)).1 hn x y
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have := hiso x (M.rep τ g y)
  rw [hcomp] at this
  simpa using this

end GlobalTheory.RepAdj
