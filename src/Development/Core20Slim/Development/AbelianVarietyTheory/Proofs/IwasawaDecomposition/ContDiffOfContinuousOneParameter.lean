module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory


open MeasureTheory Filter Topology in
open scoped ContDiff in
theorem _root_.GlobalTheory.contDiff_of_continuous_oneParameter (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (T : ℝ → A) (hT : Continuous T) (h0 : T 0 = 1)
    (hadd : ∀ s t, T (s + t) = T s * T t) : ContDiff ℝ ∞ T := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → A, G = fun x => ∫ s in (0:ℝ)..x, T s := ⟨_, rfl⟩
  have hG : ∀ x, HasDerivAt G (T x) x := fun x => by
    rw [hGdef]; exact (hT.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hG0 : G 0 = 0 := by rw [hGdef]; exact intervalIntegral.integral_same
  have hlim : Tendsto (fun δ : ℝ => δ⁻¹ • G δ) (𝓝[≠] 0) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hG 0)
    rw [h0] at h
    refine h.congr' (Eventually.of_forall fun δ => ?_)
    simp [slope_def_module, hG0]
  obtain ⟨δ, hδu, hδ0⟩ :=
    ((hlim.eventually (Units.isOpen.mem_nhds isUnit_one)).and self_mem_nhdsWithin).exists
  have hδ : δ ≠ 0 := hδ0
  have hu : IsUnit (G δ) := by
    have e : G δ = algebraMap ℝ A δ * (δ⁻¹ • G δ) := by
      rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ, one_smul]
    rw [e]
    exact ((Ne.isUnit hδ).map (algebraMap ℝ A)).mul hδu
  have key : ∀ t, T t * G δ = G (t + δ) - G t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ A (T t)).intervalIntegral_comp_comm
      (hT.intervalIntegrable (μ := volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hGdef]
    dsimp only
    rw [← h1, intervalIntegral.integral_interval_sub_left (hT.intervalIntegrable (μ := volume) _ _)
      (hT.intervalIntegrable (μ := volume) _ _)]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => T x) t, add_zero]
  have hform : T = fun t => (G (t + δ) - G t) * ↑hu.unit⁻¹ := by
    funext t
    rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hT
  | succ n ih =>
    have hGn : ContDiff ℝ (n + 1 : ℕ) G := by
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hG x).differentiableAt, by simp, ?_⟩
      rwa [show deriv G = T from funext fun x => (hG x).deriv]
    rw [hform]
    exact ((hGn.comp (contDiff_id.add contDiff_const)).sub hGn).mul contDiff_const

end GlobalTheory
