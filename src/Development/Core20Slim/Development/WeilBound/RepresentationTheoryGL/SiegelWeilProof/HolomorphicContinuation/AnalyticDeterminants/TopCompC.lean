module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.StarExpNegI
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamSing
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def matrixBlockRestriction (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ s ∧ b ∈ t then x a b else 0

def matrixBlockRestrictionLinear (s t : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixBlockRestriction s t
      map_add' := fun x y => by ext a b; simp only [matrixBlockRestriction, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext a b; simp only [matrixBlockRestriction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }

@[simp] theorem block_part_linear_apply (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : matrixBlockRestrictionLinear s t x = matrixBlockRestriction s t x := rfl

def conjL (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n)
      map_add' := fun x y => by
        simp only [map_add (f := _), ← fromBlocks_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, ← fromBlocks_smul, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem conjL_apply (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : conjL g P Q R S x = g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n) := rfl

def rotL (g : M2 n) (j : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹)
      map_add' := fun x y => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (x + y) 0 0 = fromBlocks 0 x 0 0 + fromBlocks 0 y 0 0 by
          rw [fromBlocks_add]; simp]
        simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • x) 0 0 = c • fromBlocks 0 x 0 0 by
          rw [fromBlocks_smul]; simp]
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem rotL_apply (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    rotL g j θ H = g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹) := rfl

theorem nU_eq (H : Matrix (Fin n) (Fin n) ℂ) : nU H = 1 + fromBlocks 0 H 0 0 := by
  rw [nU, ← fromBlocks_one, fromBlocks_add]; simp

theorem rot_mul_inv (j : ℕ) (θ : ℝ) : rot (n := n) j θ * (rot j θ)⁻¹ = 1 := inG_mul_inv (rot_inG j θ)

theorem rot_nU (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    g * rot j θ * nU H * (rot j θ)⁻¹ = g + rotL g j θ H := by
  simp only [nU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, rot_mul_inv, rotL_apply]

theorem rotL_single (g : M2 n) (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • rotL g j θ (single r s 1) =
      g * (Cm n * zLow j r s * CmI n) + Complex.exp (2 * θ * Complex.I) • (g * (Cm n * zMid j r s * CmI n)) +
        Complex.exp (2 * θ * Complex.I) ^ 2 • (g * (Cm n * zTop j r s * CmI n)) := by
  have hX : rot (n := n) j θ * fromBlocks 0 (single r s 1) 0 0 * (rot j θ)⁻¹ =
      rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1 := by
    have h := rot_nU (1 : M2 n) j θ (single r s 1)
    simp only [Matrix.one_mul, rotL_apply] at h
    rw [h]
    abel
  rw [rotL_apply, hX, ← Matrix.mul_smul, rot_conj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem block_part_single (s t : Finset (Fin n)) (r u : Fin n) :
    matrixBlockRestriction s t (single r u (1 : ℂ)) = if r ∈ s ∧ u ∈ t then single r u 1 else 0 := by
  ext a b
  by_cases h : r ∈ s ∧ u ∈ t
  · rw [if_pos h]
    simp only [matrixBlockRestriction, Matrix.single_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]
  · rw [if_neg h]
    simp only [matrixBlockRestriction, Matrix.single_apply, Matrix.zero_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]

theorem memB {j : ℕ} {a : Fin n} : a ∈ blkB j ↔ a ∉ blkA j := by simp [blkB]

def topL (g : M2 n) (j : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  conjL g (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkB j)) (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkA j))
    ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkB j)) ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkA j))

theorem topL_single (g : M2 n) (j : ℕ) (r s : Fin n) : topL g j (single r s 1) = g * (Cm n * zTop j r s * CmI n) := by
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, block_part_linear_apply, block_part_single, zTop]
  congr 2
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, memB, fromBlocks_smul, fromBlocks_neg]

end PositivityTheory.Rg.Sw.LVs.TC
