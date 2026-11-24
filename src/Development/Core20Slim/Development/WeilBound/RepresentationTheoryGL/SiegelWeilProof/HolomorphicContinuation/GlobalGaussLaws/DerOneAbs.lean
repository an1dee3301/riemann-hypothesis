module

public import Mathlib
public import Init.Core
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory intervalIntegral

namespace PositivityTheory.Rg.Sw.Glob.DerOneAbsH

theorem integral_deriv_zero {X Ξ : Type*} [MeasurableSpace X] [Countable Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (m : Measure X) [SFinite m] (F F' : X → ℝ → Ξ → ℂ)
    (hd : ∀ x ξ, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s => F x s ξ) (F' x t ξ) t)
    (hcont : ∀ x ξ, Continuous fun t => F' x t ξ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod (volume.restrict (Set.Ioc 0 1))))
    (hfin : ∫⁻ p : X × ℝ, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod (volume.restrict (Set.Ioc 0 1))) ≠ ⊤)
    (hsum0 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 0 ξ‖) (hsum1 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 1 ξ‖)
    (hint0 : Integrable (fun x => ∑' ξ, F x 0 ξ) m) (hint1 : Integrable (fun x => ∑' ξ, F x 1 ξ) m)
    (hends : ∫ x, ∑' ξ, F x 1 ξ ∂m = ∫ x, ∑' ξ, F x 0 ξ ∂m)
    (hconst : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x, ∑' ξ, F' x t ξ ∂m = ∫ x, ∑' ξ, F' x 0 ξ ∂m) :
    ∫ x, ∑' ξ, F' x 0 ξ ∂m = 0 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hae : ∀ ξ, AEMeasurable (fun p : X × ℝ => ‖F' p.1 p.2 ξ‖ₑ) (m.prod μ) := fun ξ => (hmeas ξ).enorm
  have hle : ∀ ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≤ ∫⁻ p, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) :=
    fun ξ => lintegral_mono fun p => ENNReal.le_tsum (f := fun ξ => ‖F' p.1 p.2 ξ‖ₑ) ξ
  have hI : ∀ ξ, Integrable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod μ) := fun ξ =>
    ⟨hmeas ξ, lt_of_le_of_lt (hle ξ) hfin.lt_top⟩
  have htsum : ∑' ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≠ ⊤ := by
    rw [← lintegral_tsum hae]; exact hfin

  have hftc : ∀ x ξ, ∫ t, F' x t ξ ∂μ = F x 1 ξ - F x 0 ξ := by
    intro x ξ
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd x ξ) ((hcont x ξ).intervalIntegrable 0 1)

  have hswap : ∀ ξ, ∫ x, (∫ t, F' x t ξ ∂μ) ∂m = ∫ t, (∫ x, F' x t ξ ∂m) ∂μ := fun ξ =>
    integral_integral_swap (f := fun x t => F' x t ξ) (hI ξ)

  have hbx : ∑' ξ, ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≤ ∫⁻ x, ∫⁻ t, ‖F' x t ξ‖ₑ ∂μ ∂m :=
          lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod _ (hae ξ)).symm
  have hbt : ∑' ξ, ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≤ ∫⁻ t, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ :=
          lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod_symm _ (hae ξ)).symm
  have S1 : ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_left.aestronglyMeasurable) hbx
  have S2 : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_right.aestronglyMeasurable) hbt

  have hslice : ∀ᵐ t ∂μ, ∀ ξ, AEStronglyMeasurable (fun x => F' x t ξ) m := by
    rw [ae_all_iff]
    intro ξ
    exact ((hmeas ξ).prod_swap).prodMk_left
  have hfinT : ∀ᵐ t ∂μ, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ≠ ⊤ := by
    have hmξ : ∀ ξ, AEMeasurable (fun t => ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := fun ξ => by
      simpa using ((hae ξ).prod_swap).lintegral_prod_right'
    have hm' : AEMeasurable (fun t => ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := AEMeasurable.tsum hmξ
    have : ∫⁻ t, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hmξ]
      refine ne_top_of_le_ne_top htsum (le_of_eq (tsum_congr fun ξ => ?_))
      exact (lintegral_prod_symm _ (hae ξ)).symm
    filter_upwards [ae_lt_top' hm' this] with t ht using ht.ne
  have S3 : ∀ᵐ t ∂μ, ∫ x, ∑' ξ, F' x t ξ ∂m = ∑' ξ, ∫ x, F' x t ξ ∂m := by
    filter_upwards [hslice, hfinT] with t h1 h2 using integral_tsum h1 h2
  have hIoc : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc

  set c := ∫ x, ∑' ξ, F' x 0 ξ ∂m with hc
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc]; simp
  have key : c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := by
    have : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∫ _t, c ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [S3, hIoc] with t h1 h2
      rw [← h1, hconst t h2]
    rw [this, MeasureTheory.integral_const, Measure.real, hμ1, ENNReal.toReal_one, one_smul]
  have hsub : ∀ᵐ x ∂m, ∑' ξ, ∫ t, F' x t ξ ∂μ = ∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ := by
    filter_upwards [hsum0, hsum1] with x h0 h1
    simp only [hftc]
    exact (h1.of_norm).tsum_sub h0.of_norm
  calc c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := key
    _ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ := S2
    _ = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m := tsum_congr fun ξ => (hswap ξ).symm
    _ = ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m := S1.symm
    _ = ∫ x, (∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ) ∂m := integral_congr_ae hsub
    _ = ∫ x, ∑' ξ, F x 1 ξ ∂m - ∫ x, ∑' ξ, F x 0 ξ ∂m := integral_sub hint1 hint0
    _ = 0 := by rw [hends, sub_self]

end PositivityTheory.Rg.Sw.Glob.DerOneAbsH
