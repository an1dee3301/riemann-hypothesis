module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel 
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelCells

variable {D : D7} {n : ℕ}

def lastDiag (R : Type) [Zero R] [One R] (n j : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if n - j ≤ i.val then 1 else 0

def wMat (R : Type) [Ring R] (n j : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  StdUnn.blk4 (1 - lastDiag R n j) (lastDiag R n j) (-lastDiag R n j) (1 - lastDiag R n j)

theorem lastDiag_mul_self (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * lastDiag R n j = lastDiag R n j := by
  simp only [lastDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem lastDiag_mul_one_sub (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * (1 - lastDiag R n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lastDiag_mul_self, sub_self]

theorem one_sub_mul_lastDiag (R : Type) [Ring R] (n j : ℕ) : (1 - lastDiag R n j) * lastDiag R n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lastDiag_mul_self, sub_self]

theorem adj_lastDiag {j : ℕ} : adj (lastDiag (AE D) n j) = lastDiag (AE D) n j := by
  ext i k
  simp only [adj, lastDiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : k = i
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem wMat_key {R : Type} [CommRing R] {n : ℕ} (L : Matrix (Fin n) (Fin n) R) (h : L * L = L) :
    StdUnn.blk4 (1 - L) (-L) L (1 - L) * StdUnn.blk4 0 1 (-1) 0 * StdUnn.blk4 (1 - L) L (-L) (1 - L) =
      StdUnn.blk4 0 1 (-1) 0 := by
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul]
  have h1 : (1 - L) * (1 - L) = 1 - L := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h, sub_self, sub_zero]
  have h2 : L * (1 - L) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have h3 : (1 - L) * L = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    add_zero, zero_add]
  congr 1
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, h2, h3, neg_zero, add_zero]
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h, h1, h2, h3]; abel
  · rw [h1, h]; abel
  · rw [h2, h3]; simp

theorem exists_wPart (j : ℕ) : ∃ g : StdUnn.G D n, StdUnn.mat g = wMat (AE D) n j := by
  have e1 := lastDiag_mul_self (AE D) n j
  have e2 := lastDiag_mul_one_sub (AE D) n j
  have e3 := one_sub_mul_lastDiag (AE D) n j
  have e4 : (1 - lastDiag (AE D) n j) * (1 - lastDiag (AE D) n j) = 1 - lastDiag (AE D) n j := by
    rw [Matrix.sub_mul, Matrix.one_mul, e2, sub_zero]
  refine StdUnn.Model.exists_mat _ (StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
    (1 - lastDiag (AE D) n j)) ?_ ?_ ?_
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · have ha : adj (wMat (AE D) n j) = StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
        (1 - lastDiag (AE D) n j) := by
      rw [wMat, StdUnn.Model.adelicConjTranspose_blockMatrixTwoByTwoFin, adj_sub, adj_one, adj_neg, adj_lastDiag]
    rw [ha]
    exact wMat_key _ e1






end GlobalTheory.SiegelCells

end
