module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

theorem PhaseOnMinus.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PhaseOnMinus.Statement ι := by
  intro H P hM c hc
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hHi : H⁻¹ * H = 1 := nonsing_inv_mul H hdet

  have hA2 : A * A = 1 := by
    simp only [hAdef, majInvolution]
    calc H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPHP, hHi]

  have hPA : P * A = H := by
    simp only [hAdef, majInvolution]; rw [← Matrix.mul_assoc, hPHP]

  have hAh : Aᴴ = P * H⁻¹ := by
    simp only [hAdef, majInvolution, conjTranspose_mul, conjTranspose_nonsing_inv,
      hH.eq, hP.isHermitian.eq]

  let Dm : ℂ → Matrix ι ι ℂ := fun a => ((1 + a) / 2) • (1 : Matrix ι ι ℂ) + ((1 - a) / 2) • A
  have hD : phaseOnMinus H P c = Dm c := by
    simp only [Dm, phaseOnMinus, ← hAdef]
    module
  have hDD : ∀ a b : ℂ, a * b = 1 → Dm a * Dm b = 1 := by
    intro a b hab
    simp only [Dm, add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hA2]
    have e1 : (1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2) = 1 := by
      linear_combination (1 / 2 : ℂ) * hab
    have e2 : (1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2) = 0 := by
      linear_combination (-1 / 2 : ℂ) * hab
    calc _ = ((1 + a) / 2 * ((1 + b) / 2) + (1 - a) / 2 * ((1 - b) / 2)) • (1 : Matrix ι ι ℂ)
          + ((1 + a) / 2 * ((1 - b) / 2) + (1 - a) / 2 * ((1 + b) / 2)) • A := by module
      _ = 1 := by rw [e1, e2]; simp
  have hDA : ∀ a : ℂ, Dm a * A = A * Dm a := by
    intro a
    simp only [Dm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one]

  have hDP : (Dm c)ᴴ * P = P * Dm (star c) := by
    simp only [Dm, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hAh, add_mul,
      mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hPA]
    simp only [hPHP, star_div₀, star_add, star_sub, star_one]
    norm_num
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, hDP, Matrix.mul_assoc, hDD _ _ hcc, Matrix.mul_one]
  · rw [hD, ← hPA, ← Matrix.mul_assoc, hDP, Matrix.mul_assoc, ← hDA c, ← Matrix.mul_assoc,
      Matrix.mul_assoc P, hDD _ _ hcc, Matrix.mul_one]
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module
  · intro u hu
    rw [hD]
    simp only [Dm, add_mulVec, smul_mulVec, one_mulVec, hu]
    module

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
