module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawC
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockMatrixDiagonalOneEqOne
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FinitePartAdelicPointMatrix
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem mat_mOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (A : GL (Fin n) ℂ) :
    mat (ι (mOf A)) = blk4 (unitAt hσ τ A).1 0 0 (adj ((unitAt hσ τ A)⁻¹).1) := by
  have hU : ((unitAt hσ τ A).1).map (finPart D) = 1 := by
    rw [unitAt_val]
    exact finite_part_adelic_point_matrix hσ τ A.1
  have hUi : (((unitAt hσ τ A)⁻¹).1).map (finPart D) = 1 := finite_part_adelic_point_matrix hσ τ (A⁻¹).1
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 (mOf A)).2.2, finite_part_block_matrix_map, hU, finPart_adj _ hUi, Matrix.map_zero _ (map_zero _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 (mOf A)).1, mR_mOf, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_matrix hσ,
        compAt_zero]
      have hUc : compAt θ τ ((unitAt hσ τ A)⁻¹).1 = (A⁻¹).1 := component_adelic_point_matrix hσ τ (A⁻¹).1
      rw [hUc]
      rfl
    · rw [(hι.2 (mOf A)).2.1 τ' e, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_ne hσ e,
        compAt_zero]
      have hUc : compAt θ τ' ((unitAt hσ τ A)⁻¹).1 = 1 := component_adelic_point_ne hσ e (A⁻¹).1
      rw [hUc, Matrix.conjTranspose_one, block_matrix_diagonal_one_eq_one]

theorem mat_nOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (y : PositivityTheory.Rg.Sw.GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks 1 b 0 1) : mat (ι y) = blk4 1 (atT σ τ b) 0 1 := by
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 y).2.2, finite_part_block_matrix_map, finPart_atT_map hσ τ b, Matrix.map_zero _ (map_zero _),
      Matrix.map_one _ (map_zero _) (map_one _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 y).1, hy, component_block_matrix (R := ℂ), compAt_one, compAt_atT hσ, compAt_zero]
      rfl
    · rw [(hι.2 y).2.1 τ' e, component_block_matrix (R := ℂ), compAt_one, compAt_atT_ne hσ e, compAt_zero, block_matrix_diagonal_one_eq_one]

end PositivityTheory.Rg.Sw.Glob.LocLawH
