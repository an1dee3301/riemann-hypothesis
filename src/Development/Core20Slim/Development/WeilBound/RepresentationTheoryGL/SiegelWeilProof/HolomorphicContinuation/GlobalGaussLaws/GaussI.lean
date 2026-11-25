module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussG
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussD
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussF
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem siegelOrb : SiegelOrb := by
  intro n Z hZ
  obtain ⟨S, hSS, hSu⟩ := exists_sqrt (show ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef from hZ)
  set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Z + Zᴴ) with hXdef
  have hX : Xᴴ = X := conj_half_smul Z
  have hSu' : IsUnit Sᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hSu.star
  refine ⟨mkGR (nU X) (by rw [det_nU]; exact one_ne_zero) (inG_nU hX) * mkGR (mM S) (det_mM hSu) (inG_mM hSu), ?_, ?_⟩
  · rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₂₁_mul]
    simp [nU, mM]
  · unfold actZ
    rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
    simp only [nU, mM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    rw [Matrix.nonsing_inv_nonsing_inv _ hSu', Matrix.add_mul, Matrix.mul_assoc X, Matrix.nonsing_inv_mul _ hSu',
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hXdef, smul_smul]
    have hc : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
      norm_num
    rw [hc, ← smul_add, show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]
    norm_num

end PositivityTheory.Rg.Sw.Glob
