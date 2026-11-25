module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem tubeGood_tsum (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace T] (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ))
    (hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g)
    (hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2)
    (hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) :
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) := by fun_prop
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v τ₀ hτ₀
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hτ₀ g
    have hline : Continuous fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re) :=
      hc.comp (by fun_prop : Continuous fun τ : ℂ => p + τ • v)
    have hS : (fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re)) ⁻¹' V ∈ 𝓝 τ₀ :=
      hline.continuousAt.preimage_mem_nhds hV
    obtain ⟨S, hSsub, hSo, hτS⟩ := mem_nhds_iff.1 hS
    have hd : DifferentiableOn ℂ (fun τ : ℂ => ∑' r, t r (p + τ • v) g) S :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun r => (hhol r g p v).differentiableOn) hSo
        (fun r τ hτ => hb _ (hSsub hτ) g (mem_of_mem_nhds hU) r)
    exact ((hd τ₀ hτS).differentiableAt (hSo.mem_nhds hτS)).differentiableWithinAt
  · rintro ⟨l₀, g₀⟩ ⟨hl₀, -⟩
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl₀ g₀
    have hVl : (fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V ∈ 𝓝 l₀ :=
      hc.continuousAt.preimage_mem_nhds hV
    have hS : ((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U ∈ 𝓝 (l₀, g₀) :=
      prod_mem_nhds hVl hU
    have hd : ContinuousOn (fun y : (ℂ × ℂ) × T => ∑' r, t r y.1 y.2)
        (((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U) :=
      continuousOn_tsum (fun r => (hcont r).continuousOn) hu
        (fun r y hy => hb _ hy.1 _ hy.2 r)
    exact (hd.continuousAt hS).continuousWithinAt
  · intro C hCΩ hC g
    refine hC.induction_on
      (p := fun S => ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ PositivityTheory.RgEis.tube S, ∀ g' ∈ U,
        ‖∑' r, t r l g'‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨Set.univ, univ_mem, 0, fun l hl => hl.elim⟩
    · rintro s s' hss ⟨U, hU, M, hM⟩
      exact ⟨U, hU, M, fun l hl g' hg' => hM l (hss hl) g' hg'⟩
    · rintro s s' ⟨U, hU, M, hM⟩ ⟨U', hU', M', hM'⟩
      refine ⟨U ∩ U', inter_mem hU hU', max M M', ?_⟩
      rintro l (hl | hl) g' hg'
      · exact (hM l hl g' hg'.1).trans (le_max_left _ _)
      · exact (hM' l hl g' hg'.2).trans (le_max_right _ _)
    · intro x hx
      obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom x (hCΩ hx) g
      exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, U, hU, ∑' r, u r, fun l hl g' hg' =>
        tsum_of_norm_bounded hu.hasSum (fun r => hb l hl g' hg' r)⟩
  · intro l hl g
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl g
    exact Summable.of_nonneg_of_le (fun r => norm_nonneg _)
      (fun r => hb l (show (l.1.re, l.2.re) ∈ V from mem_of_mem_nhds hV) g (mem_of_mem_nhds hU) r) hu

end GlobalTheory.CompanionTheory.RgEisCross
