module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_one_add_sq_eq_prod_eigenvalues (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    Matrix.det (1 + b * b) = ((∏ i, (1 + hb.eigenvalues i ^ 2) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hb.eigenvalues i : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hb.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hb.eigenvectorUnitary
  have hs : b = U * D * star U := by
    have := hb.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have h1 : 1 + b * b = U * (1 + D * D) * star U := by
    rw [hs]
    calc 1 + U * D * star U * (U * D * star U)
        = U * star U + U * D * (star U * U) * D * star U := by
          rw [hUU']; simp only [Matrix.mul_assoc]
      _ = U * (1 + D * D) * star U := by
          rw [hUU]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hdet : (star U).det * U.det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have h2 : 1 + D * D = Matrix.diagonal (fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ)) := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext i
    push_cast
    ring
  rw [h1, Matrix.det_mul, Matrix.det_mul, h2, Matrix.det_diagonal]
  push_cast
  calc U.det * (∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2)) * (star U).det
      = ((star U).det * U.det) * ∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem one_le_detW : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  intro n b hb
  unfold detW
  rw [det_one_add_sq_eq_prod_eigenvalues n b hb, Complex.ofReal_re]
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ 1 + hb.eigenvalues i ^ 2 := fun i _ => by
    nlinarith [sq_nonneg (hb.eigenvalues i)]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) this

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
