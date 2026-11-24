module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open MeasureTheory Filter Topology Set

variable {H : Type*} [MeasurableSpace H]

def fz (r : H → ℝ) (u : H → ℂ) (s₀ z : ℂ) (b : H) : ℂ := (r b : ℂ) ^ (-(z - s₀)) * u b

theorem norm_cpow_le {x : ℝ} (hx : 1 ≤ x) {R : ℝ} (hR : x ≤ R) (w : ℂ) :
    ‖(x : ℂ) ^ w‖ ≤ R ^ max w.re 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc x ^ w.re ≤ x ^ max w.re 0 := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    _ ≤ R ^ max w.re 0 := Real.rpow_le_rpow (by linarith) hR (le_max_right _ _)

theorem integrableOn_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r)
    (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H} (hS : MeasurableSet S)
    (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) (z : ℂ) : IntegrableOn (fz r u s₀ z) S ν := by
  have hmeas : Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) :=
    (Complex.measurable_ofReal.comp hrm).pow_const _
  refine Measure.integrableOn_of_bounded (M := Rm ^ max (-(z - s₀)).re 0 * C) hSf.ne
    (hmeas.aestronglyMeasurable.mul hum) ?_
  filter_upwards [ae_restrict_mem hS] with b hb
  show ‖(r b : ℂ) ^ (-(z - s₀)) * u b‖ ≤ Rm ^ max (-(z - s₀)).re 0 * C
  rw [norm_mul]
  exact mul_le_mul (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le (hr1 b) (hRm b hb) _) (hub b)
    (norm_nonneg _) (Real.rpow_nonneg (by linarith [hr1 b, hRm b hb]) _)

theorem differentiable_setIntegral_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b)
    (hrm : Measurable r) (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H}
    (hS : MeasurableSet S) (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) :
    Differentiable ℂ (fun z => ∫ b in S, fz r u s₀ z b ∂ν) := by
  intro z₀
  haveI : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.mpr hSf.ne
  have hofr : Measurable fun b => (r b : ℂ) := Complex.measurable_ofReal.comp hrm
  have hmeas : ∀ z : ℂ, Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) := fun z => hofr.pow_const _
  set R' := max Rm 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 ≤ R' := by linarith
  set E := max (s₀.re - z₀.re + 1) 0 with hE
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν.restrict S)
    (F := fun z b => PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b)
    (F' := fun z b => -(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b))
    (bound := fun _ => R' * R' ^ E * C) (x₀ := z₀)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => ((hmeas z).aestronglyMeasurable.mul hum).restrict)
    (PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hub hS hSf hRm z₀)
    ((((Complex.measurable_log.comp hofr).mul (hmeas z₀)).aestronglyMeasurable.mul hum).neg.restrict)
    ?_ (integrable_const _) ?_
  · exact key.2.differentiableAt
  · filter_upwards [ae_restrict_mem hS] with b hb z hz
    show ‖-(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b)‖ ≤ R' * R' ^ E * C
    have hb1 := hr1 b
    have hbR : r b ≤ R' := (hRm b hb).trans (le_max_left _ _)
    have hlog : ‖Complex.log (r b)‖ ≤ R' := by
      rw [← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hb1)]
      linarith [Real.log_le_sub_one_of_pos (show 0 < r b by linarith)]
    have hre : (-(z - s₀)).re ≤ s₀.re - z₀.re + 1 := by
      have h1 : dist z z₀ < 1 := Metric.mem_ball.mp hz
      rw [Complex.dist_eq] at h1
      have h2 := Complex.abs_re_le_norm (z - z₀)
      rw [Complex.sub_re, abs_le] at h2
      rw [Complex.neg_re, Complex.sub_re]
      linarith [h2.1]
    have hcp : ‖(r b : ℂ) ^ (-(z - s₀))‖ ≤ R' ^ E :=
      (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le hb1 hbR _).trans
        (Real.rpow_le_rpow_of_exponent_le hR'1 (max_le_max hre le_rfl))
    rw [norm_neg, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hlog hcp (norm_nonneg _) hR'0) (hub b) (norm_nonneg _)
      (mul_nonneg hR'0 (Real.rpow_nonneg hR'0 _))
  · refine Eventually.of_forall fun b z _ => ?_
    have hne : (r b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hr1 b])
    have h0 := (((hasDerivAt_id' z).sub_const s₀).neg.const_cpow (c := (r b : ℂ)) (Or.inl hne)).mul_const (u b)
    show HasDerivAt (fun x => (r b : ℂ) ^ (-(x - s₀)) * u b)
      (-(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b)) z
    have e : (r b : ℂ) ^ (-(z - s₀)) * Complex.log (r b) * -1 * u b =
        -(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b) := by ring
    exact h0.congr_deriv e

theorem core (ν : Measure H) (r : H → ℝ) (u : H → ℂ) (s₀ w₀ : ℂ) (B : ℕ → Set H)
    (hBm : ∀ j, MeasurableSet (B j)) (hmono : Monotone B) (hcov : ⋃ j, B j = univ)
    (hfin : ∀ j, ν (B j) < ⊤) (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r) (hrb : ∀ j, ∃ Rm, ∀ b ∈ B j, r b ≤ Rm)
    (hum : AEStronglyMeasurable u ν) (hub : ∃ C, ∀ b, ‖u b‖ ≤ C)
    (hshell : ∀ z j, ∫ b in B (j + 1) \ B j, fz r u s₀ z b ∂ν = 0)
    (hint : ∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (fz r u s₀ z) ν)
    (hval : Tendsto (fun j => ∫ b in B j, u b ∂ν) atTop (𝓝 w₀)) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W s₀ = w₀ ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (fz r u s₀ z) ν ∧ W z = ∫ b, fz r u s₀ z b ∂ν := by
  obtain ⟨C, hC⟩ := hub
  have hon : ∀ z j, IntegrableOn (PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z) (B j) ν := fun z j => by
    obtain ⟨Rm, hRm⟩ := hrb j
    exact PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hC (hBm j) (hfin j) hRm z
  have hG : ∀ z j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν =
      ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := by
    intro z j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih]
      have hsub : B j ⊆ B (j + 1) := hmono (Nat.le_succ j)
      rw [← Set.union_diff_cancel hsub, setIntegral_union Set.disjoint_sdiff_right
        ((hBm _).diff (hBm _)) (hon z j) ((hon z (j + 1)).mono_set diff_subset), hshell, add_zero]
  obtain ⟨R0, hR0⟩ := hrb 0
  refine ⟨fun z => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν,
    PositivityTheory.SiegelWeilFormula.SwLocFin.differentiable_setIntegral_fz hr1 hrm hum hC (hBm 0) (hfin 0) hR0, ?_, ?_⟩
  · have hfs : ∀ j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν = ∫ b in B j, u b ∂ν := by
      intro j
      simp only [PositivityTheory.SiegelWeilFormula.SwLocFin.fz, sub_self, neg_zero, Complex.cpow_zero, one_mul]
    have e : (fun j => ∫ b in B j, u b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν := by
      funext j
      rw [← hfs j, hG]
    rw [e] at hval
    exact tendsto_nhds_unique tendsto_const_nhds hval
  · obtain ⟨t, ht⟩ := hint
    refine ⟨t, fun z hz => ⟨ht z hz, ?_⟩⟩
    have hlim := tendsto_setIntegral_of_monotone hBm hmono (ht z hz).integrableOn
    rw [hcov, Measure.restrict_univ] at hlim
    have e : (fun j => ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := funext (hG z)
    rw [e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim

end PositivityTheory.SiegelWeilFormula.SwLocFin
