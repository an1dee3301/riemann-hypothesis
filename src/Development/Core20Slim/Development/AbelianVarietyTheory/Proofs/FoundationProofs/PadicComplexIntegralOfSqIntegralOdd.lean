module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_two_Cp_eq_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := (map_natCast _ 2).symm
  have h2 : (2 : ℂ_[p]) = ((2 : ℕ) : ℂ_[p]) := by norm_num
  rw [h2, h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp

theorem intSer_of_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff H = 1) (hH : IntSer (H ^ 2)) : IntSer H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    set f : ℕ × ℕ → ℂ_[p] := fun q => PowerSeries.coeff q.1 H * PowerSeries.coeff q.2 H with hf
    have hsq : PowerSeries.coeff n (H ^ 2) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q := by
      rw [pow_two, PowerSeries.coeff_mul]
    have m1 : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    have m2 : (n, (0 : ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n) := by
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, add_zero, and_true, ne_eq, Prod.mk.injEq]
      omega
    have c0 : PowerSeries.coeff 0 H = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
    set S := ∑ q ∈ ((Finset.HasAntidiagonal.antidiagonal n).erase (0, n)).erase (n, 0), f q with hS
    have hdec : PowerSeries.coeff n (H ^ 2) = 2 * PowerSeries.coeff n H + S := by
      rw [hsq, ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]
      simp only [hf, c0, one_mul, mul_one]
      ring
    have hSle : ‖S‖ ≤ 1 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro q hq
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a, b⟩ := q
      simp only [Prod.mk.injEq, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2 hq3
      have ha : a < n := by omega
      have hb : b < n := by omega
      simp only [hf, norm_mul]
      exact mul_le_one₀ (ih a ha) (norm_nonneg _) (ih b hb)
    have h2 : ‖2 * PowerSeries.coeff n H‖ = ‖PowerSeries.coeff n H‖ := by
      rw [norm_mul, norm_two_Cp_eq_one p hp, one_mul]
    have e : 2 * PowerSeries.coeff n H = PowerSeries.coeff n (H ^ 2) - S := by rw [hdec]; ring
    rw [← h2, e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hH n) ?_)
    rw [norm_neg]; exact hSle

theorem intSer_of_sq_main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p],
    PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H :=
  fun p _ hp H h0 hH => intSer_of_sq p hp H h0 hH

end GlobalTheory.EvenTheta
