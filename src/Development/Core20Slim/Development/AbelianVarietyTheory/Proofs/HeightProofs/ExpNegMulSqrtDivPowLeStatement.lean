module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpNegMulSqrtDivPowLe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt : ∀ (a : ℝ) (D : ℕ), 0 < a → ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) / (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.exp_neg_mul_sqrt_div_pow_le | exact GlobalTheory.exp_neg_mul_sqrt_div_pow_le | (intros; apply GlobalTheory.exp_neg_mul_sqrt_div_pow_le <;> assumption)
