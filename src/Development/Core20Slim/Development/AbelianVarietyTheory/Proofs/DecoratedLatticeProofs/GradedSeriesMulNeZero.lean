module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology Metric Set

namespace GlobalTheory

theorem gradedSeries_mul_ne_zero : ∀ (ι : Type) (deg : ι → ℕ) (a : ι → ℂ) (ρ δ : ℝ) (P Q : ℂ → ℂ), 0 < δ → Differentiable ℂ P → Differentiable ℂ Q → (∀ r : ℝ, 0 < r → r < ρ → Summable fun i => ‖a i‖ * r ^ deg i) → (∀ x : ℝ, 0 < x → x < δ → (∑' i, a i * (x : ℂ) ^ deg i) * P x = Q x) → ∀ X : ℂ, ‖X‖ < ρ → Q X ≠ 0 → P X ≠ 0 := by
  intro ι deg a ρ δ P Q hδ hP hQ hsum hid X hX hQX
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  set F : ℂ → ℂ := fun z => ∑' i, a i * z ^ deg i with hFdef
  have hFd : ∀ z ∈ ball (0 : ℂ) ρ, DifferentiableAt ℂ F z := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have hr0 : 0 < (‖z‖ + ρ) / 2 := by positivity
    have hrρ : (‖z‖ + ρ) / 2 < ρ := by linarith
    have hD : DifferentiableOn ℂ F (ball 0 ((‖z‖ + ρ) / 2)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hsum _ hr0 hrρ)
        (fun i => (differentiable_const _ |>.mul (differentiable_id.pow _)).differentiableOn)
        isOpen_ball (fun i w hw => ?_)
      rw [mem_ball_zero_iff] at hw
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw.le _) (norm_nonneg _)
    exact hD.differentiableAt (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))
  set G : ℂ → ℂ := fun z => F z * P z - Q z with hGdef
  have hGan : AnalyticOnNhd ℂ G (ball 0 ρ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    exact (((hFd z hz).mul (hP z)).sub (hQ z)).differentiableWithinAt
  have hs0 : 0 < min δ ρ := lt_min hδ hρ
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), G z = 0 := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hs0] with x hx
    have h1 := hid x hx.1 (lt_of_lt_of_le hx.2 (min_le_left _ _))
    simp only [G, F, h1, sub_self]
  have heq := hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected (mem_ball_self hρ) hfreq
  have hGX : G X = 0 := heq (by rw [mem_ball_zero_iff]; exact hX)
  intro hPX
  apply hQX
  simp only [G, hPX, mul_zero, zero_sub, neg_eq_zero] at hGX
  exact hGX

end GlobalTheory
