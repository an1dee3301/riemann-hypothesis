module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
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
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}



theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
    rw [Complex.star_def, Complex.conj_I]
    linear_combination (-1 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
  exact Matrix.PosDef.one

theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₁₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₁] using this

theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₁₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₁₂] using this

theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  have := congrArg toBlocks₂₁ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₁] using this

theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have := congrArg toBlocks₂₂ (fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁
    M.toBlocks₂₂ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂)
  simpa only [fromBlocks_toBlocks, toBlocks_fromBlocks₂₂] using this

theorem mR_mul (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

theorem inG_mR (y : GR n) : InG (mR y) := y.2

theorem num_den_mul (M N : M2 n) (Z W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) = N.toBlocks₁₁ * Z + N.toBlocks₁₂) :
    (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) ∧
    (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by
  rw [toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
  constructor
  · have e : (M.toBlocks₁₁ * W + M.toBlocks₁₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₁₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₁₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring
  · have e : (M.toBlocks₂₁ * W + M.toBlocks₂₂) * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) =
        M.toBlocks₂₁ * (W * (N.toBlocks₂₁ * Z + N.toBlocks₂₂)) +
          M.toBlocks₂₂ * (N.toBlocks₂₁ * Z + N.toBlocks₂₂) := by noncomm_ring
    rw [e, hW]
    noncomm_ring

end PositivityTheory.Rg.Sw.Glob.GaussH
