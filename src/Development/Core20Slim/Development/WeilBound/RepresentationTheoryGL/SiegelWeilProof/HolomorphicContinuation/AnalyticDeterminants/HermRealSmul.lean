module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
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
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem inG_mul {a b : M2 n} (ha : InG a) (hb : InG b) : InG (a * b) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [ha, hb]

theorem inG_upper {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (fromBlocks 1 b 0 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hb]

theorem inG_lower {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hc]

theorem inG_scalar {c : ℂ} (hc : star c * c = 1) : InG (c • (1 : M2 n)) := by
  show (c • (1 : M2 n))ᴴ * JJ n * (c • (1 : M2 n)) = JJ n
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hc, one_smul]

theorem upper_line (y : M2 n) (b : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 b 0 0) = y * fromBlocks 1 (t • b) 0 1 := by
  have e : (fromBlocks 1 (t • b) 0 1 : M2 n) = 1 + t • fromBlocks 0 b 0 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem lower_line (y : M2 n) (c : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 0 c 0) = y * fromBlocks 1 0 (t • c) 1 := by
  have e : (fromBlocks 1 0 (t • c) 1 : M2 n) = 1 + t • fromBlocks 0 0 c 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem herm_real_smul {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) (t : ℝ) : ((t : ℂ) • b)ᴴ = (t : ℂ) • b := by
  rw [conjTranspose_smul, hb]
  simp

private theorem fderiv_apply_eq_zero_of_const_on_real_line {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : E → W} {y v : E}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const v).const_add y
    convert h0 using 1
    · rfl
    · rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
  have h1 : HasFDerivAt f ((fderiv ℂ f y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hc := h1.comp_hasDerivAt (0 : ℝ) hl
  have hk : (f ∘ fun t : ℝ => y + (t : ℂ) • v) = fun _ => f y := funext h
  rw [hk] at hc
  exact ((hasDerivAt_const (0 : ℝ) (f y)).unique hc).symm

theorem fderiv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {f : M2 n → W} {y v : M2 n}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  exact fderiv_apply_eq_zero_of_const_on_real_line hf h

end PositivityTheory.Rg.Sw.LVs.HolB
