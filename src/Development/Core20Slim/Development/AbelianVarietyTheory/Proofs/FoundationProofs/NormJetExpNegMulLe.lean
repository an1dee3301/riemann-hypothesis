module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
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
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ExpJets

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expPS_eq_subst (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    expPS F = (PowerSeries.exp ℂ_[p]).subst F := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' hF), expPS, coeff_mk,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp, div_eq_inv_mul]
  · intro k hk
    by_contra h
    apply hk
    have hlt : n < k := by simpa using h
    have h0 : coeff n (F ^ k) = 0 := by
      have : (X : PowerSeries ℂ_[p]) ^ k ∣ F ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.2 hF) k
      exact X_pow_dvd_iff.1 this n hlt
    simp [h0]

theorem derivative_expPS (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    d⁄dX (expPS F) = expPS F * d⁄dX F := by
  rw [expPS_eq_subst F hF, PowerSeries.derivative_subst (HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp]

theorem norm_jet_mul_le (A B : PowerSeries ℂ_[p]) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, i + j = n →
      ‖(i.factorial : ℂ_[p]) * coeff i A‖ * ‖(j.factorial : ℂ_[p]) * coeff j B‖ ≤ C) :
    ‖(n.factorial : ℂ_[p]) * coeff n (A * B)‖ ≤ C := by
  rw [coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun x hx => ?_
  obtain ⟨i, j⟩ := x
  have hij : i + j = n := by simpa using hx
  have e : (n.factorial : ℂ_[p]) * (coeff i A * coeff j B) =
      (((i + j).choose j : ℕ) : ℂ_[p]) *
        (((i.factorial : ℂ_[p]) * coeff i A) * ((j.factorial : ℂ_[p]) * coeff j B)) := by
    rw [← hij, ← Nat.add_choose_mul_factorial_mul_factorial i j]
    push_cast
    ring
  simp only
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(((i + j).choose j : ℕ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  calc _ ≤ 1 * C := mul_le_mul h1 (h i j hij) (by positivity) zero_le_one
    _ = C := one_mul C

theorem jet_derivative (A : PowerSeries ℂ_[p]) (n : ℕ) :
    (n.factorial : ℂ_[p]) * coeff n (d⁄dX A) =
      ((n + 1).factorial : ℂ_[p]) * coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem norm_jet_expPS_le (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) (s : ℝ)
    (hs : 0 ≤ s) (h : ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * coeff n F‖ ≤ s ^ n) (n : ℕ) :
    ‖(n.factorial : ℂ_[p]) * coeff n (expPS F)‖ ≤ s ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expPS]
    | succ n =>
      rw [← jet_derivative, derivative_expPS F hF]
      refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
      rw [jet_derivative, ← hij, add_assoc, pow_add]
      exact mul_le_mul (ih i (by omega)) (h (j + 1)) (norm_nonneg _) (by positivity)

theorem norm_jet_exp_neg_mul_le : ∀ (p : ℕ) [Fact p.Prime] (ph : PowerSeries ℂ_[p]) (s : ℝ), 1 ≤ s → PowerSeries.constantCoeff ph = 0 → (∀ i, i ≠ 2 → ‖(i.factorial : ℂ_[p]) * PowerSeries.coeff i ph‖ ≤ 1) → ‖(2 : ℂ_[p]) * PowerSeries.coeff 2 ph‖ ≤ s ^ 2 → ∀ (f : PowerSeries ℂ_[p]), (∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (expPS (-ph) * f)‖ ≤ s ^ n := by
  intro p _ ph s hs h0 h1 h2 f hf n
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hE := norm_jet_expPS_le (-ph) (by simp [h0]) s hs0 fun m => by
    rw [map_neg, mul_neg, norm_neg]
    by_cases hm : m = 2
    · subst hm
      simpa using h2
    · exact (h1 m hm).trans (one_le_pow₀ hs)
  refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
  rw [← hij, pow_add]
  exact mul_le_mul (hE i) ((hf j).trans (one_le_pow₀ hs)) (norm_nonneg _) (by positivity)

end GlobalTheory.ExpJets
