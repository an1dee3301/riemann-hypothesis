module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Max
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Asymptotics NumberField

private theorem UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO (K : Type*) [Field K] [NumberField K] :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  have hlim := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ))
      =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ _ hlim
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd (Nat.cast_eq_zero.mp h) hn
  simp only [Real.rpow_one]
  refine IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) hO
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)
      ≤ ∑ k ∈ Finset.Icc 0 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left zero_le_one)
          fun _ _ _ ↦ by positivity
    _ = _ := by
        rw [← Nat.cast_sum, ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
        simp [Set.coe_eq_subtype]

private theorem UpperTheory.Reformulated.B.Qp7.summable_count_mul (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ σ)⁻¹ := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (σ : ℂ))
    (UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO K) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (by simpa using hσ)
  refine h.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (zero_lt_one.trans hσ).ne']
  · simp [div_eq_mul_inv]

theorem UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {σ : ℝ},
    (1 : ℝ) < σ →
      Summable fun (I : Ideal (NumberField.RingOfIntegers K)) ↦
        ((↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) I) : ℝ) ^ σ)⁻¹ := by
  intro K _ _ σ hσ
  have hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun n ↦ (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply]; positivity)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  refine (UpperTheory.Reformulated.B.Qp7.summable_count_mul K hσ).congr fun n ↦ ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((Ideal.absNorm I.1 : ℝ) ^ σ)⁻¹ = ((n : ℝ) ^ σ)⁻¹ := fun I ↦ by rw [I.2]
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, this, tsum_const, nsmul_eq_mul]
