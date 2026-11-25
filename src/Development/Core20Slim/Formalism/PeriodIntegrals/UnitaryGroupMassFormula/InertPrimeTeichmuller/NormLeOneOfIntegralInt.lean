module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField

noncomputable section

namespace PI.OkpW

theorem norm_le_one_of_integral {F R : Type*} [NormedField F] [IsUltrametricDist F] [CommRing R]
    [Algebra R F] (hR : ∀ r : R, ‖algebraMap R F r‖ ≤ 1) (δ : F) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨f, hf, hfe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one,
    one_mul] at hfe
  have h1 : δ ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hfe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap R F (f.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ f.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ f.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R F (f.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ f.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ f.natDegree / ‖δ‖ < ‖δ‖ ^ f.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ f.natDegree‖ = ‖δ‖ ^ f.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

theorem norm_le_one_of_integral_int {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra ℤ F]
    (δ : F) (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral (fun n => by
    rw [eq_intCast (algebraMap ℤ F) n]; exact IsUltrametricDist.norm_intCast_le_one F n) δ h

variable {p : ℕ} [hp : Fact p.Prime]


variable {K : Type} [Field K] [NumberField K]

theorem norm_tau_le (τ : K →+* ℂ_[p]) (a : 𝓞 K) : ‖τ (a : K)‖ ≤ 1 :=
by
  have hI : IsIntegral ℤ (τ (a : K)) := by
    obtain ⟨f, hm, he⟩ := RingOfIntegers.isIntegral_coe a
    refine ⟨f, hm, ?_⟩
    have := congrArg τ he
    rw [Polynomial.hom_eval₂, map_zero] at this
    rwa [Subsingleton.elim (τ.comp (algebraMap ℤ K)) (algebraMap ℤ ℂ_[p])] at this
  exact norm_le_one_of_integral_int _ hI








end PI.OkpW
