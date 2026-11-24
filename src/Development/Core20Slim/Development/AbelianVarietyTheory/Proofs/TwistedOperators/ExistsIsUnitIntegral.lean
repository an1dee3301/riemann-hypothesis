module

public import Mathlib
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
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
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NormedSpace Filter Topology

namespace GlobalTheory.ExponentialIntegralUnits

universe u_1

variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_primitive (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem exists_isUnit_integral (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1) :
    ∃ δ : ℝ, IsUnit (∫ s in (0 : ℝ)..δ, M s) := by
  have hd := (hasDerivAt_primitive M hc 0).tendsto_slope_zero
  rw [h0] at hd
  have hev := hd.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨δ, hδU, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : δ ≠ 0 := Set.mem_compl_singleton_iff.1 hδ0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hδU
  refine ⟨δ, ?_⟩
  have e : (∫ s in (0 : ℝ)..δ, M s) = algebraMap ℝ 𝔸 δ * (δ⁻¹ • ∫ s in (0 : ℝ)..δ, M s) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  rw [e]
  exact ((isUnit_iff_ne_zero.2 hδ0').map (algebraMap ℝ 𝔸)).mul hδU

theorem mul_integral (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by
  have hL := ((ContinuousLinearMap.mul ℝ 𝔸) (M t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
  simp only [ContinuousLinearMap.mul_apply'] at hL
  rw [← hL]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_left (fun s => M s) t, add_zero,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]

theorem exists_hasDerivAt (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, HasDerivAt M (M t * X) t := by
  obtain ⟨δ, hA⟩ := exists_isUnit_integral M hc h0
  have hAA : (∫ s in (0 : ℝ)..δ, M s) * ↑(hA.unit⁻¹) = 1 := hA.mul_val_inv
  refine ⟨(M δ - 1) * ↑(hA.unit⁻¹), fun t => ?_⟩
  have hM : ∀ u, M u = ((∫ s in (0 : ℝ)..(u + δ), M s) - ∫ s in (0 : ℝ)..u, M s) * ↑(hA.unit⁻¹) := fun u => by
    rw [← mul_integral M hc hadd u δ, mul_assoc, hAA, mul_one]
  have hP : HasDerivAt (fun u => ∫ s in (0 : ℝ)..(u + δ), M s) (M (t + δ)) t := by
    first
      | exact (hasDerivAt_primitive M hc (t + δ)).comp_add_const t δ
      | exact HasDerivAt.comp_add_const t δ (hasDerivAt_primitive M hc (t + δ))
  have hF := (hP.sub (hasDerivAt_primitive M hc t)).mul_const (↑(hA.unit⁻¹) : 𝔸)
  have hF' := hF.congr_of_eventuallyEq (Eventually.of_forall hM)
  refine hF'.congr_deriv ?_
  rw [hadd, ← mul_assoc, mul_sub, mul_one]

theorem exists_exp_eq (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M (0 : ℝ) = (1 : 𝔸))
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, NormedSpace.exp (t • X) = M t := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨X, hX⟩ := exists_hasDerivAt M hc h0 hadd
  refine ⟨X, fun t => ?_⟩
  have hN : ∀ u : ℝ, HasDerivAt (fun v => M v * NormedSpace.exp (v • (-X))) 0 u := fun u => by
    have h3 := (hX u).mul (hasDerivAt_exp_smul_const (-X) u)
    refine h3.congr_deriv ?_
    have hcomm : Commute (NormedSpace.exp (u • (-X))) X :=
      (((Commute.refl X).neg_left).smul_left u).exp_left
    rw [mul_neg, hcomm.eq, mul_neg, ← mul_assoc, add_neg_cancel]
  have hconst : ∀ u, M u * NormedSpace.exp (u • (-X)) = 1 := fun u => by
    have h4 := is_const_of_deriv_eq_zero (fun v => (hN v).differentiableAt) (fun v => (hN v).deriv) u 0
    rw [h4, h0, zero_smul, NormedSpace.exp_zero, one_mul]
  have hinv : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute ((((Commute.refl X).neg_left).smul_left t).smul_right t), smul_neg,
      neg_add_cancel, NormedSpace.exp_zero]
  calc NormedSpace.exp (t • X) = (M t * NormedSpace.exp (t • (-X))) * NormedSpace.exp (t • X) := by
        rw [hconst t, one_mul]
    _ = M t := by rw [mul_assoc, hinv, mul_one]

end GlobalTheory.ExponentialIntegralUnits
