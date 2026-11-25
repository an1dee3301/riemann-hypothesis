module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_norm_pow_mul_le_sqrt_weighted_sq :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  intro E F _ _ _ _ _ μ _ _
  set s : ℕ := finrank ℝ E + 1 with hs
  have hfin : ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ < ∞ := by
    apply finite_integral_one_add_norm
    rw [hs]; push_cast
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    linarith
  set A := ∫⁻ z : E, ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) ∂μ with hA
  set B : ℝ≥0∞ := ENNReal.ofReal (2 ^ (2 * s - 1)) with hB
  refine ⟨A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  intro H hH k
  let f : E → ℝ≥0∞ := fun z => ENNReal.ofReal (((1 + ‖z‖) ^ s)⁻¹)
  let g : E → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖))
  have hf : AEMeasurable f μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    exact ((measurable_const.add measurable_norm).pow_const s).inv
  have hg : AEMeasurable g μ := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have h1 : ∀ z, (f * g) z = ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) := by
    intro z
    have hp : 0 < (1 + ‖z‖) ^ s := by positivity
    simp only [Pi.mul_apply, f, g]
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have h2 : ∀ z, f z ^ (2 : ℝ) = ENNReal.ofReal ((1 + ‖z‖) ^ (-((2 * s : ℕ) : ℝ))) := by
    intro z
    simp only [f]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, inv_pow, ← pow_mul,
      mul_comm]
  have h3 : ∀ z, g z ^ (2 : ℝ) ≤ B * (ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) +
      ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2)) := by
    intro z
    simp only [g, hB]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := add_pow_le (zero_le_one) (norm_nonneg z) (2 * s)
    rw [Real.rpow_two, add_assoc, ← hs]
    calc ((1 + ‖z‖) ^ s * (‖z‖ ^ k * ‖H z‖)) ^ 2
        = (1 + ‖z‖) ^ (2 * s) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by ring
      _ ≤ (2 ^ (2 * s - 1) * (1 ^ (2 * s) + ‖z‖ ^ (2 * s))) * (‖z‖ ^ k * ‖H z‖) ^ 2 := by
        gcongr
      _ = _ := by rw [one_pow]; ring
  simp only [h1, h2] at key
  refine key.trans ?_
  rw [← hA, mul_assoc, ← ENNReal.mul_rpow_of_nonneg B _ (by norm_num)]
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))
  have hm : Measurable fun z : E => ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    fun_prop
  rw [← lintegral_add_left hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono h3

end GlobalTheory
