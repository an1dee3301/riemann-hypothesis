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
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace UpperTheory.Reformulated.B.P6.r23b

theorem pow_mul_exp_le_half_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : ℝ), 0 ≤ x →
      (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) := by
  refine ⟨(2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2), by positivity, ?_⟩
  intro x hx
  have hy : 0 ≤ a / 2 * (1 + x) := by positivity
  have h1 : (a / 2 * (1 + x)) ^ N / (N.factorial : ℝ) ≤ Real.exp (a / 2 * (1 + x)) := Real.pow_div_factorial_le_exp (x := a / 2 * (1 + x)) (n := N) hy
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h1' : (a / 2 * (1 + x)) ^ N ≤ Real.exp (a / 2 * (1 + x)) * (N.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h1
  have h2 : (1 + x) ^ N = (2 / a) ^ N * (a / 2 * (1 + x)) ^ N := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hp : (0 : ℝ) ≤ (2 / a) ^ N := by positivity
  have h3 : (1 + x) ^ N ≤ (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x)) := by
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1' hp
    linarith [this]
  have h4 : Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x)) =
      Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (1 + x) ^ N * Real.exp (-(a * x))
      ≤ ((2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x))) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / a) ^ N * (N.factorial : ℝ) * (Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x))) := by ring
    _ = (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
        rw [h4]; ring

theorem PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp :
    ∀ (N : ℕ) (a : ℝ), OfNat.ofNat (nat_lit 0) < a → ∃ (C : ℝ), OfNat.ofNat (nat_lit 0) ≤ C ∧ ∀ (x : ℝ), OfNat.ofNat (nat_lit 0) ≤ x → (OfNat.ofNat (nat_lit 1) + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / OfNat.ofNat (nat_lit 2) * x)) := by
  intro N a ha
  exact pow_mul_exp_le_half_exp N a ha

end UpperTheory.Reformulated.B.P6.r23b
