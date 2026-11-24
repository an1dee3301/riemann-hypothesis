module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
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
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory.RingOfIntegersNormBound

theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq, hqx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hqx
  have hlead : q.coeff q.natDegree = 1 := hq
  rw [hlead, map_one, one_mul] at hqx
  have hpow : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hqx
  have hpos : 0 < ‖x‖ := lt_trans one_pos hlt
  have key : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)
      rw [norm_mul, norm_pow]
      have h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)
      calc ‖algebraMap ℤ F (q.coeff n)‖ * ‖x‖ ^ n ≤ 1 * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖x‖ ^ n := one_mul _
        _ < _ := h1
  have := key q.natDegree
  rw [← norm_neg, ← hpow, norm_pow] at this
  exact lt_irrefl _ this

theorem norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))

end GlobalTheory.RingOfIntegersNormBound
