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
public import Mathlib.Algebra.Order.Ring.Defs
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

namespace Bl.SecondBlockLemmaN

theorem goal1 :
  ∀ (z : Complex),
  (∀ (n : Nat), LT.lt.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} z n) 1)) (1 / 2)) → Eq.{1} z 1 := by
  intro z h
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hx := h (2 ^ k)
      have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * ((z ^ (2 ^ k) - 1) + 2) := by
        rw [pow_succ, pow_mul]; ring
      rw [e, norm_mul]
      have h3 : ‖(2 : ℂ)‖ ≤ ‖(z ^ (2 ^ k) - 1) + 2‖ + ‖z ^ (2 ^ k) - 1‖ := by
        have := norm_sub_le ((z ^ (2 ^ k) - 1) + 2) (z ^ (2 ^ k) - 1)
        simpa using this
      have h4 : ‖(2 : ℂ)‖ = 2 := by simp
      have h2 : (3 / 2 : ℝ) ≤ ‖(z ^ (2 ^ k) - 1) + 2‖ := by linarith
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖(z ^ (2 ^ k) - 1) + 2‖ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have h6 : 1 < (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) := (div_lt_iff₀ (by positivity)).mp hk
  have h7 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
  have h8 := key k
  have h9 := h (2 ^ k)
  linarith

end Bl.SecondBlockLemmaN
