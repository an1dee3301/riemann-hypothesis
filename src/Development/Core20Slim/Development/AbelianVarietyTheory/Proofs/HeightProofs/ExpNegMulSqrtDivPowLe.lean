module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory

theorem exp_neg_mul_sqrt_div_pow_le (a : ℝ) (D : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) /
      (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  refine ⟨Real.exp a * ((D + 1).factorial : ℝ) / a ^ (D + 1), fun m => ?_⟩
  set s : ℝ := (m : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by rw [hs]; have := m.cast_nonneg (α := ℝ); linarith
  have hs0 : 0 < s := by linarith
  set x : ℝ := s ^ (-(1 / 2 : ℝ)) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hs0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have hx2 : x ^ 2 * s = 1 := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  have hmx : (m : ℝ) * x = x⁻¹ - x := by
    have : (m : ℝ) = s - 1 := by rw [hs]; ring
    rw [this]; field_simp; nlinarith [hx2]
  set n := D + 1 with hn
  have hK : 0 < Real.exp a * (n.factorial : ℝ) / a ^ n := by positivity

  have hpow := Real.pow_div_factorial_le_exp (a / x) (by positivity) n
  have hexp : Real.exp (-(a * m * x)) * Real.exp (a / x) ≤ Real.exp a := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : a * m * x = a * (x⁻¹ - x) := by rw [mul_assoc, hmx]
    rw [this, div_eq_mul_inv]
    nlinarith
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have h1 : Real.exp (-(a * m * x)) * ((a / x) ^ n / n.factorial) ≤ Real.exp a :=
    le_trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hexp
  have h2 : Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_pow, div_div, mul_div_assoc', div_le_iff₀ (by positivity)] at h1
    have e : Real.exp a * (n.factorial : ℝ) / a ^ n * x * x ^ D
        = Real.exp a * (x ^ n * n.factorial) / a ^ n := by
      rw [hn, pow_succ]; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [h1]

  have hxs : x ≤ Real.sqrt x := by
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0.le).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
  calc Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := h2
    _ ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hxs hK.le

end GlobalTheory
