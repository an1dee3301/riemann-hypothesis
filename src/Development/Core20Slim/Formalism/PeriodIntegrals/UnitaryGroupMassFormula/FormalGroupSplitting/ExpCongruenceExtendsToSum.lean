module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.AddPreservesExpCongruence
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglPhSplit
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Development
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit

variable {K : Type} [Field K]

def AllIn (W : Subring K) {σ : Type} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ W

theorem allIn_mul {W : Subring K} {σ : Type} {F G : MvPowerSeries σ K} (hF : AllIn W F)
    (hG : AllIn W G) : AllIn W (F * G) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hF _) (hG _)

theorem expMv_eq_subst [CharZero K] {σ : Type} {F : MvPowerSeries σ K}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv F = PowerSeries.subst F (PowerSeries.exp K) := by
  classical
  ext α
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [coeff_expMv, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra hc
    apply hn
    have hdeg : (α.sum fun _ k => k) = Finsupp.degree α := rfl
    rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      (by rw [pow_one]; exact hF) (by omega), smul_zero]

section Rename₂

variable {ι ι' : Type} [Fintype ι]

variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0


end Rename₂

end PI.FglPhSplit.Wk

end
