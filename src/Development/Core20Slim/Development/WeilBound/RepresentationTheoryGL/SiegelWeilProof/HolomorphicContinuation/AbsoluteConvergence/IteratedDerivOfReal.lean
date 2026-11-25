module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.TSA

theorem iteratedDeriv_ofReal' {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {h : ℝ → ℂ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hFh : ∀ x : ℝ, F x = h x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧ ∀ x : ℝ, iteratedDeriv p F x = iteratedDeriv p h x := by
  induction p with
  | zero => simpa using ⟨hF, hFh⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y) (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = iteratedDeriv p h := funext he
      rw [h4] at h3
      exact h3.deriv.symm

theorem eq_of_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h : ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0) (t : ℝ) : f t = g t := by
  have h0U : (0 : ℂ) ∈ U := by simpa using hmem 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hnear : f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball), ← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball)]
    simp_rw [h]
  set V := connectedComponentIn U (0 : ℂ)
  have hVo : IsOpen V := hU.connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have h0V : (0 : ℂ) ∈ V := mem_connectedComponentIn h0U
  have hRV : range (fun x : ℝ => (x : ℂ)) ⊆ V := by
    apply (isPreconnected_range Complex.continuous_ofReal).subset_connectedComponentIn
    · exact ⟨0, by simp⟩
    · rintro _ ⟨x, rfl⟩; exact hmem x
  have hVU : V ⊆ U := connectedComponentIn_subset _ _
  have hfa : AnalyticOnNhd ℂ f V := (hf.mono hVU).analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := (hg.mono hVU).analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc h0V hnear (hRV ⟨t, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt.TSA
