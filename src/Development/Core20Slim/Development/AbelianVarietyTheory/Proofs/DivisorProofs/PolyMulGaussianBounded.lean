module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.PolynomialGaussianBounded

theorem poly_mul_gaussian_bounded :
    ∀ (c : ℝ), (0 : ℝ) < c → ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r →
      ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : ((1 : ℝ) + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    calc ((1 : ℝ) + r) ^ N ≤ (Real.exp r) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp ((N : ℝ) * r) := by rw [← Real.exp_nat_mul]
  calc ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ)))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ (2 : ℕ))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * c * r - N)]

end GlobalTheory.PolynomialGaussianBounded
