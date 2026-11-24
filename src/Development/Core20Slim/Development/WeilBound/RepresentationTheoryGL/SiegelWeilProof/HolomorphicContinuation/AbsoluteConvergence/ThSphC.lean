module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
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
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

theorem anNhd_iter {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r f) V := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.analyticOnNhd hV).iterated_deriv r

theorem real_iter (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hR : ∀ s : ℝ, (s : ℂ) ∈ V)
    (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => f t) = fun s : ℝ => iteratedDeriv r f s := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [iteratedDeriv_succ]
    have hd : DifferentiableAt ℂ (iteratedDeriv n f) (s : ℂ) :=
      ((anNhd_iter hV hf n) s (hR s)).differentiableAt
    exact hd.hasDerivAt.comp_ofReal.deriv

theorem helpC : HelpC := by
  refine ⟨fun f V hV hR hf r s => congrFun (real_iter f V hV hR hf r) s, ?_⟩
  intro f V hV hR hf h0 s
  have hA := hf.analyticOnNhd hV
  have h0V : (0 : ℂ) ∈ V := by simpa using hR 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball)]
    simp [h0]
  have hpre : IsPreconnected (Set.range ((↑) : ℝ → ℂ)) :=
    (isConnected_range Complex.continuous_ofReal).isPreconnected
  have hsub := hpre.subset_connectedComponentIn (x := (0 : ℂ)) ⟨0, by simp⟩
    (by rintro _ ⟨t, rfl⟩; exact hR t)
  have hEq := (hA.mono (connectedComponentIn_subset V 0)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn (mem_connectedComponentIn h0V) hloc
  simpa using hEq (hsub ⟨s, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt
