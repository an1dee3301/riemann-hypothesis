module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAc
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix

namespace GlobalTheory.RealWeil

theorem mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0:ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᵀ)) (NormedSpace.exp ((0:ℝ) • Xᵀ) * Xᵀ) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᵀ 0
  have h3 := (h1.mul_const (Matrix.J l ℝ)).mul h2
  have h4 : ((fun t : ℝ => NormedSpace.exp (t • X) * Matrix.J l ℝ) * fun t : ℝ => NormedSpace.exp (t • Xᵀ)) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.mem_iff.1 (h t)
    rw [← Matrix.exp_transpose, Matrix.transpose_smul] at this
    exact this
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0:ℝ) (Matrix.J l ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h5
  have hJ := Matrix.J_squared l ℝ
  have h6 : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X) := by
    have h7 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = 0 := by
      rw [h5]; simp
    have h8 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ
        = Matrix.J l ℝ * X * (Matrix.J l ℝ * Matrix.J l ℝ) + (Matrix.J l ℝ * Matrix.J l ℝ) * Xᵀ * Matrix.J l ℝ := by
      noncomm_ring
    rw [h8, hJ] at h7
    simp only [mul_neg, mul_one, neg_mul, one_mul] at h7 ⊢
    rw [← neg_add, neg_eq_zero] at h7
    exact eq_neg_of_add_eq_zero_right h7
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact h6

end GlobalTheory.RealWeil
