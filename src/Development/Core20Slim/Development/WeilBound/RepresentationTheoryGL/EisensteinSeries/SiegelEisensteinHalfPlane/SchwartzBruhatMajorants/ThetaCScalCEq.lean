module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.MeasurePreservingCompEquiv
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinRankN.Hd

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_scalC (a : IdeleGroup k) :
    Matrix.GeneralLinearGroup.det (scalC a : GL ι 𝔸[k]) = a ^ Fintype.card ι := by
  ext
  simp [scalC, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]

theorem tInv_scalC (a : IdeleGroup k) :
    tInv (scalC a : GL ι 𝔸[k]) = scalC a⁻¹ := by
  ext i j
  simp only [tInv, MonoidHom.coe_mk, OneHom.coe_mk, scalC, ← map_inv, Units.coe_map]
  show (Matrix.scalar ι ((↑a⁻¹ : 𝔸[k])))ᵀ i j = Matrix.scalar ι ((↑a⁻¹ : 𝔸[k])) i j
  rw [Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem thetaC_scalC_eq {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (a : IdeleGroup k) :
    thetaC F (scalC a) =
      ((((ideleModule k a : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) : ℂ) *
        thetaC (adelicFourierPi k F) (scalC a⁻¹) := by
  have hA := GlobalTheory.T.linearChange_mem_schwartzBruhatPi hF (scalC a : GL ι 𝔸[k])
  have h := tsum_algebraMap_eq_tsum_adelicFourierPi hA
  rw [GlobalTheory.CompanionTheory.LtrFourier.Hd.adelicFourierPi_ltr, tInv_scalC, det_scalC] at h
  have e1 : thetaC F (scalC a) =
      ∑' ξ : ι → k, ltr (scalC a : GL ι 𝔸[k]) F (fun i => algebraMap k 𝔸[k] (ξ i)) := rfl
  have e2 : thetaC (adelicFourierPi k F) (scalC a⁻¹) =
      ∑' ξ : ι → k, ltr (scalC a⁻¹ : GL ι 𝔸[k]) (adelicFourierPi k F) (fun i => algebraMap k 𝔸[k] (ξ i)) := rfl
  rw [e1, h, e2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  rw [map_pow]
  simp only [Positive.val_pow, Complex.ofReal_pow, Complex.ofReal_inv]

end GlobalTheory.CompanionTheory.EpsteinRankN.Hd
