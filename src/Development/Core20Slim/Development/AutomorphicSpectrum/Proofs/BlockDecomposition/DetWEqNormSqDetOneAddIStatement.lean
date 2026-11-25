module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddI
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_eq_normSq_det_one_add_I : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul <;> assumption)
