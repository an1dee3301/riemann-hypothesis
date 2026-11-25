module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormula
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_block_matrix_formula : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    Matrix.det (1 + Complex.I • b) ≠ 0 → ∀ (v : Fin n → ℂ) (d : ℝ),
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM <;> assumption)
