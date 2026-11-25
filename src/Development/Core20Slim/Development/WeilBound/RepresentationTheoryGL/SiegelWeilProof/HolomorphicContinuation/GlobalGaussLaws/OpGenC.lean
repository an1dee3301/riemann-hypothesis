module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisati
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
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

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem compAt_zero' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j
  simp [compAt]

theorem compAt_one' (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} : compAt θ τ (1 : Mx D n n) = 1 := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem compAt_J (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} :
    compAt θ τ (blk4 (0 : Mx D n n) 1 (-1) 0) = blk4 0 1 (-1) 0 := by
  rw [component_block_matrix, GlobalTheory.RealParamSize.compAt_neg, compAt_zero', compAt_one']

theorem fin_J {n : ℕ} : (blk4 (0 : Mx D n n) 1 (-1) 0).map (finPart D) = blk4 0 1 (-1) 0 := by
  rw [finite_part_block_matrix, Matrix.map_neg _ (map_neg (finPart D)), Matrix.map_zero _ (map_zero (finPart D)),
    Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))]

theorem iota_conj {θ : InfFam D} {τ : D.what₂.Tau} {n : ℕ} {ι : GR n →* G D n} (hθ : IsInfFam θ)
    (hι : IsPlaceEmb θ τ ι) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (y yn : GR n) (c : Matrix (Fin n) (Fin n) ℂ)
    (hyc : mR y = nbar c) (hyn : mR yn = nU (-c)) : ι yn = w⁻¹ * ι y * w := by
  apply g_ext
  have hm : mat (w⁻¹ * ι y * w) = mat w⁻¹ * mat (ι y) * mat w := rfl
  rw [hm, mat_inv_w w hw, hw]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 yn).2.2, (hι.2 y).2.2, Matrix.map_neg _ (map_neg (finPart D)), fin_J, mul_one,
      neg_mul, jsq, neg_neg]
  · intro τ'
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.RealParamSize.compAt_neg, compAt_J]
    by_cases h : τ' = τ
    · subst h
      rw [(hι.2 yn).1, (hι.2 y).1, hyn, hyc]
      change blk4 1 (-c) 0 1 = -blk4 0 1 (-1) 0 * blk4 1 0 c 1 * blk4 0 1 (-1) 0
      rw [neg_block_matrix, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul]
      simp
    · rw [(hι.2 yn).2.1 τ' h, (hι.2 y).2.1 τ' h, mul_one, neg_mul, jsq, neg_neg]

end PositivityTheory.Rg.Sw.Glob.OG
