module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGauTwistedConv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Complex
open scoped InnerProductSpace Real

namespace GlobalTheory.RealWeil

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace H] in
theorem IsHeis.inner_left (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (u : V) (x y : H) :
    ⟪ρ u x, y⟫_ℂ = ⟪x, ρ (-u) y⟫_ℂ := by
  have h0 : omJ J u (-u) = 0 := by
    have := omJ_skew hJ u u
    have e : omJ J u (-u) = -omJ J u u := by simp [omJ]
    linarith
  have e : ρ u (ρ (-u) y) = y := by
    rw [h.2.1, h0, add_neg_cancel, h.1]
    simp
  have := (⟨(ρ u : H →ₗ[ℂ] H), h.2.2.1 u⟩ : H →ₗᵢ[ℂ] H).inner_map_map x (ρ (-u) y)
  rw [← this]
  change _ = ⟪ρ u x, ρ u (ρ (-u) y)⟫_ℂ
  rw [e]

theorem inner_proj_right {om : V → V → ℝ} (h : IsHeis om ρ) (x y : H) :
    ⟪x, proj h y⟫_ℂ = ∫ u, gau u * ⟪x, ρ u y⟫_ℂ := by
  rw [proj_apply, ← integral_inner (h.integrable y)]
  simp only [inner_smul_right]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem conj_gau (u : V) : (starRingEnd ℂ) (gau u) = gau u := by
  unfold gau
  rw [← Complex.exp_conj]
  simp [map_ofNat]

theorem inner_proj_left (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x y : H) :
    ⟪proj h x, y⟫_ℂ = ⟪x, proj h y⟫_ℂ := by
  rw [← inner_conj_symm, inner_proj_right, inner_proj_right, ← integral_conj,
    ← integral_neg_eq_self (fun u => gau u * ⟪x, ρ u y⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, conj_gau, inner_conj_symm, gau_neg, h.inner_left hJ]

theorem integral_gau_mul_gau : ∫ u : V, gau u * gau u = 1 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := V) (b := (π : ℂ))
    (by simpa using Real.pi_pos)
  rw [div_self hpi, one_cpow] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gau, ← Complex.exp_add]
  congr 1
  ring

theorem proj_idem (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x : H) :
    proj h (proj h x) = proj h x := by
  have := proj_heis_proj hJ h 0 x
  rwa [h.1, gau_zero, one_smul] at this

theorem proj_eq_self_of_vacuum (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {v : H}
    (hv : ∀ a, ⟪v, ρ a v⟫_ℂ = gau a * ⟪v, v⟫_ℂ) : proj h v = v := by
  have h1 : ⟪v, proj h v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [inner_proj_right]
    simp only [hv, ← mul_assoc]
    rw [integral_mul_const, integral_gau_mul_gau, one_mul]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right,
    inner_proj_left hJ, inner_proj_left hJ, proj_idem hJ, h1]
  ring

theorem eq_zero_of_orthogonal_translates_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {x : H}
    (hx : ∀ y a, ⟪ρ a (proj h y), x⟫_ℂ = 0) : x = 0 := by
  have h1 : ∀ a, proj h (ρ (-a) x) = 0 := fun a => by
    refine ext_inner_left ℂ fun y => ?_
    rw [← inner_proj_left hJ, ← h.inner_left hJ, hx, inner_zero_right]
  have hg : Good h x := fun n => by simp [h1]
  rw [← hg.inversion hJ]
  simp [h1]

end Abstract

theorem gau_toLp {ι : Type} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    gau z = Complex.exp (-(Real.pi / 2) * ∑ a, ((‖z a‖ ^ 2 : ℝ) : ℂ)) := by
  rw [gau, ← ofReal_sum, ← EuclideanSpace.norm_sq_eq]
  push_cast
  rfl

end GlobalTheory.RealWeil
