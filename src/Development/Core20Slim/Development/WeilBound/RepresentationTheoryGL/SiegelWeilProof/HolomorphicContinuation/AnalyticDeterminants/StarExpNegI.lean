module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatC
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Notation
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem exp_neg_I (t : ℂ) : Complex.exp (-t * Complex.I) = (Complex.exp (t * Complex.I))⁻¹ := by
  rw [neg_mul, Complex.exp_neg]

theorem star_exp_I (θ : ℝ) : star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem star_exp_negI (θ : ℝ) : star (Complex.exp (-θ * Complex.I)) * Complex.exp (-θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

def dA (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)

def dB (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)

theorem rot_eq (j : ℕ) (θ : ℝ) : rot (n := n) j θ = Cm n * fromBlocks (diagonal (dA j θ)) 0 0 (diagonal (dB j θ)) * CmI n := rfl

theorem dA_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dA j θ a ≠ 0 := by unfold dA; split_ifs <;> exact Complex.exp_ne_zero _

theorem dB_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dB j θ a ≠ 0 := by unfold dB; split_ifs <;> exact Complex.exp_ne_zero _

theorem rot_inG (j : ℕ) (θ : ℝ) : InG (rot (n := n) j θ) := by
  rw [rot_eq]
  refine inG_conjDiag _ _ (fun a => ?_) (fun a => ?_)
  · unfold dA; split_ifs
    · exact star_exp_I θ
    · exact star_exp_negI θ
  · unfold dB; split_ifs
    · exact star_exp_negI θ
    · exact star_exp_I θ

theorem smul_conjCm (c : ℂ) (X : M2 n) : c • (Cm n * X * CmI n) = Cm n * (c • X) * CmI n := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem rot_conj (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • (rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1) =
      Cm n * (zLow j r s + Complex.exp (2 * θ * Complex.I) • zMid j r s +
        Complex.exp (2 * θ * Complex.I) ^ 2 • zTop j r s) * CmI n := by
  rw [rot_eq, conj_nU _ _ (dA_ne j θ) (dB_ne j θ), smul_conjCm]
  congr 2
  have he : Complex.exp (2 * θ * Complex.I) = Complex.exp (θ * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu0 : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [he]
  simp only [dA, dB, zLow, zMid, zTop, blkB, Finset.mem_compl, exp_neg_I]
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, fromBlocks_smul, fromBlocks_add, fromBlocks_neg, smul_single, fromBlocks_inj]
  all_goals constructor <;> congr 1 <;> field_simp <;> ring

end PositivityTheory.Rg.Sw.LVs.TC
