module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.CancelDenoms.Core
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

namespace GlobalTheory.IterativeScalingBound

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (2 + (w - 1)) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖2 + (w - 1)‖ := by
    have t := norm_sub_le (2 + (w - 1)) (w - 1)
    have e2 : (2 + (w - 1)) - (w - 1) = (2 : ℂ) := by ring
    rw [e2] at t
    have : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have h0 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  nlinarith

theorem main : ∀ (z : ℂ), (∀ (k : ℕ), ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have key : ∀ k : ℕ, (3/2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have e : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2 := by rw [pow_succ 2 n, pow_mul]
      rw [e, pow_succ (3/2 : ℝ) n]
      calc (3/2 : ℝ) ^ n * (3/2) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ 2 ^ n - 1‖ := by gcongr
        _ ≤ _ := step _ (h n)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key k
  have h2 := h k
  have h3 : 1 / 2 < (3/2 : ℝ) ^ k * ‖z - 1‖ := by rwa [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterativeScalingBound
