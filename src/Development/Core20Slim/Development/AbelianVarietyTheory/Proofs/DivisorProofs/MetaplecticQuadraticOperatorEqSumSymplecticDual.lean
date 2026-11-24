module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

namespace GlobalTheory

theorem quad_eq_sum_symplDual (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ))
    (h : ∀ w, ∑ i, sympl (v i) w • u i = w) :
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  have hJ : ∀ (x : l ⊕ l → ℝ) (b : l ⊕ l), sympl x (Matrix.J l ℝ *ᵥ Pi.single b 1) = x b := by
    intro x b
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.one_apply]
  have hcol : ∀ b, ∑ i, v i b • u i = Matrix.J l ℝ *ᵥ Pi.single b 1 := by
    intro b
    have := h (Matrix.J l ℝ *ᵥ Pi.single b 1)
    simp only [hJ] at this
    exact this
  have hcoef : ∀ a b, ∑ i, (X *ᵥ u i) a * v i b = (X * Matrix.J l ℝ) a b := by
    intro a b
    have := congrArg (fun w => (X *ᵥ w) a) (hcol b)
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_mulVec] at this
    have e : ((X * Matrix.J l ℝ) *ᵥ Pi.single b 1) a = (X * Matrix.J l ℝ) a b := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← e, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hT : ∀ i, dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i) =
      ∑ a, ∑ b, (((X *ᵥ u i) a * v i b : ℝ) : ℂ) •
        (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := by
    intro i
    rw [dRho_eq_sum (X *ᵥ u i), dRho_eq_sum (v i)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    conv_lhs => arg 1; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    module
  rw [quad]
  congr 1
  simp_rw [hT, ← hcoef, Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

end GlobalTheory
