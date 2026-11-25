module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem sq_le_sum_enorm_sq_lintegral_bound
    (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ) (hg : ∀ a, Continuous (g a))
    (hfg : ∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  by_cases hi : MeasureTheory.Integrable (fun x => f x ^ 2) μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
      (MeasureTheory.ae_of_all _ (fun x => sq_nonneg (f x)))]
    have hm : ∀ a, Measurable (fun x => ‖g a x‖ₑ ^ 2) := fun a =>
      ((hg a).measurable.enorm).pow_const 2
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 ∂μ := by
          refine MeasureTheory.lintegral_mono (fun x => ?_)
          calc ENNReal.ofReal (f x ^ 2) ≤ ENNReal.ofReal (C * ∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_le_ofReal (hfg x)
            _ = ENNReal.ofReal C * ENNReal.ofReal (∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_mul' (Finset.sum_nonneg (fun a _ => sq_nonneg _))
            _ = ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
                congr 1
                refine Finset.sum_congr rfl (fun a _ => ?_)
                rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
          rw [MeasureTheory.lintegral_const_mul _ (Finset.measurable_sum _ (fun a _ => hm a))]
          congr 1
          exact MeasureTheory.lintegral_finsetSum Finset.univ (fun a _ => hm a)
  · rw [MeasureTheory.integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

end GlobalTheory
