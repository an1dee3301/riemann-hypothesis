module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

theorem block_matrix_mul_comm_ring {R : Type} [Ring R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_diagonal_one_eq_one {R : Type} [Ring R] {n : ℕ} : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 1 0 0 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_map {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]
  rfl

theorem map_neg_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
  change (f.mapMatrix) (-1) = -1
  rw [map_neg, map_one]

theorem map_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (1 : Matrix (Fin n) (Fin n) R).map f = 1 := by
  change (f.mapMatrix) 1 = 1
  rw [map_one]

theorem blockMatrixTwoByTwoFin_transpose {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob


open LocCellA in
theorem wEx : WEx := by
  intro D n
  let M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 1 (-1) 0
  let Mi : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 (-1) 1 0
  have h1 : M * Mi = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  have h2 : Mi * M = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  let u : GL (Fin (n + n)) (AE D) := ⟨M, Mi, h1, h2⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    have hJ : JR (AF D.host.F) (Jst D n) = M := by
      simp [JR, Jst, M, block_matrix_map, map_neg_one', map_one']
    rw [hJ]
    simp [Formalism.UG.cT, M, block_matrix_map, blockMatrixTwoByTwoFin_transpose, block_matrix_mul_comm_ring, map_neg_one', map_one']
  exact ⟨⟨u, hu⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
