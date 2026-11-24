module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

open Set Filter Topology

theorem vanish_at_one_of_derivs_vanish_of_growth (φ : ℕ → ℝ → ℂ) (a b : ℝ)
    (hd : ∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) (h0 : ∀ k, φ k 0 = 0)
    (hb : ∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) : φ 0 1 = 0 := by
  set M : ℕ → ℝ := fun n => Real.sqrt (b * a ^ n * n.factorial) with hM
  have base : ∀ k t, ‖φ k t‖ ≤ M k := by
    intro k t
    have := Real.abs_le_sqrt (hb k t)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have key : ∀ m k, ∀ t ∈ Icc (0:ℝ) 1, ‖φ k t‖ ≤ M (k + m) * t ^ m / m.factorial := by
    intro m
    induction m with
    | zero => intro k t _; simpa using base k t
    | succ m ih =>
      intro k
      have hB : ∀ x, HasDerivAt (fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
          (M ((k + 1) + m) * x ^ m / m.factorial) x := by
        intro x
        have h1 := ((hasDerivAt_pow (m + 1) x).const_mul (M (k + (m + 1)))).div_const
          ((m + 1).factorial : ℝ)
        refine h1.congr_deriv ?_
        rw [show k + 1 + m = k + (m + 1) by ring]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
        have : (m.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ k)
        (f' := φ (k + 1)) (a := 0) (b := 1)
        (fun x _ => (hd k x).continuousAt.continuousWithinAt)
        (fun x _ => (hd k x).hasDerivWithinAt)
        (B := fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
        (by simp [h0 k]) hB
        (fun x hx => ih (k + 1) x (Ico_subset_Icc_self hx))
      exact this
  have hn : ∀ n : ℕ, ‖φ 0 1‖ ^ 2 ≤ b * (a ^ n / n.factorial) := by
    intro n
    have h := key n 0 1 (by simp)
    simp only [zero_add, one_pow, mul_one] at h
    have hX : 0 ≤ b * a ^ n * n.factorial := le_trans (by positivity) (hb n 1)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [div_pow, hM, Real.sq_sqrt hX] at h2
    refine h2.trans (le_of_eq ?_)
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have ht : Tendsto (fun n : ℕ => b * (a ^ n / n.factorial)) atTop (𝓝 (b * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop a).const_mul b
  rw [mul_zero] at ht
  have hle : ‖φ 0 1‖ ^ 2 ≤ 0 := ge_of_tendsto' ht hn
  have : ‖φ 0 1‖ = 0 := by nlinarith [norm_nonneg (φ 0 1)]
  exact norm_eq_zero.mp this

end GlobalTheory
