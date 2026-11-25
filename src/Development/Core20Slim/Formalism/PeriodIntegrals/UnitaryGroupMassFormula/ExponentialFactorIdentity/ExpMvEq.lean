module

public import Development.Core20Slim.Formalism.PeriodIntegrals.PhiCubeOfFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.CoeffSingleLg
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglPhSplit
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination.Lemmas
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
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PI.PhiCubeOfFactor.Wk

open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared

variable {p : ℕ} [Fact p.Prime]

theorem logMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : logMv F = logS F := rfl

theorem expMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := rfl

theorem main : Lemma := by
  intro p _ l ex E Q hex0 hinv hE1 hfun hQ
  obtain ⟨n, hnI, hn0, rfl⟩ := hQ
  have hl0 := l_constantCoeff hex0 hinv
  have hcX : ∀ i : Fin 2, constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => constantCoeff_X i
  have hlg : ∀ i : Fin 2, constantCoeff (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := by
    intro i
    unfold lg
    rw [constantCoeff_subst_of_zero (hcX i)]
    exact hl0
  have hs0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg l (Xv 1)) = 0 := by
    rw [map_add (f := _), hlg, hlg, add_zero]
  have hd0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) - lg l (Xv 1)) = 0 := by
    rw [map_sub, hlg, hlg, sub_zero]
  have hA0 : constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold add pt
    rw [constantCoeff_subst_of_zero hs0]
    exact hex0
  have hB0 : constantCoeff (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold sub pt
    rw [constantCoeff_subst_of_zero hd0]
    exact hex0
  obtain ⟨k, hk, hlk⟩ := exists_coeff_ne hex0 hinv
  have hc0 : ∀ i : Fin 2, coeff (Finsupp.single (0 : Fin 2) k) (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) =
      if i = 0 then PowerSeries.coeff k l else 0 := fun i => coeff_single_lg l 0 i hk
  have hAne : (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold add pt
    refine subst_ne_zero hex0 hinv hs0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_add (f := _), map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hBne : (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold sub pt
    refine subst_ne_zero hex0 hinv hd0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_sub, map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hcanc : eAt E (add l ex (Xv 0) (Xv 1)) * eAt E (sub l ex (Xv 0) (Xv 1)) =
      n * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hAne hBne)
    linear_combination hfun
  have hexp0 : PI.FglPhSplit.expMv (0 : PowerSeries ℂ_[p]) = 1 := by
    refine MvPowerSeries.ext fun α => ?_
    change (∑ m ∈ Finset.range ((α.sum fun _ k => k) + 1),
      MvPowerSeries.coeff α ((0 : PowerSeries ℂ_[p]) ^ m) / (m.factorial : ℂ_[p])) = MvPowerSeries.coeff α 1
    rw [Finset.sum_eq_single 0 (fun m _ hm => by rw [zero_pow hm, map_zero, zero_div])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h)]
    simp
  have hL0 : constantCoeff (logS E) = 0 := constantCoeff_logS E
  have hnL0 : constantCoeff (-logS E) = 0 := by rw [map_neg, hL0, neg_zero]
  have hUE : PI.FglPhSplit.expMv (-logS E) * E = 1 := by
    have h := expMv_add' hnL0 hL0
    rw [neg_add_cancel, hexp0, expMv_logS hE1] at h
    exact h.symm
  have hsub : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (phAt E a) * eAt E a = 1 := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, expMv_subst' ha hnL0, ← PowerSeries.subst_mul hS, hUE, ← PowerSeries.coe_substAlgHom hS,
      map_one]
  have hneg : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (-phAt E a) = eAt E a := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, ← PowerSeries.coe_substAlgHom hS, ← map_neg, neg_neg, PowerSeries.coe_substAlgHom hS,
      expMv_subst' ha hL0, expMv_logS hE1]
  have hph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (phAt E a) = 0 := by
    intro a ha
    unfold phAt
    rw [constantCoeff_subst_of_zero ha, logMv_eq]
    exact hnL0
  have hnph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (-phAt E a) = 0 := by
    intro a ha
    rw [map_neg, hph0 a ha, neg_zero]
  have hf : phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) -
      (2 * phAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + 2 * phAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) + -phAt E (Xv 0) + -phAt E (Xv 0) +
        -phAt E (Xv 1) + -phAt E (Xv 1) := by ring
  refine ⟨?_, ?_⟩
  · rw [hf, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hph0 _ hA0, hph0 _ hB0, hnph0 _ (hcX 0),
      hnph0 _ (hcX 1)]
    ring
  · rw [expMv_eq, hf]
    have c1 := hph0 _ hA0
    have c2 := hph0 _ hB0
    have c3 := hnph0 _ (hcX 0)
    have c4 := hnph0 _ (hcX 1)
    rw [expMv_add' (by simp only [map_add (f := _), c1, c2, c3, c4, add_zero]) c4,
      expMv_add' (by simp only [map_add (f := _), c1, c2, c3, add_zero]) c4,
      expMv_add' (by simp only [map_add (f := _), c1, c2, c3, add_zero]) c3,
      expMv_add' (by simp only [map_add (f := _), c1, c2, add_zero]) c3,
      expMv_add' c1 c2, hneg _ (hcX 0), hneg _ (hcX 1)]
    refine int_of_mul_eq_one hnI hn0 ?_
    have e1 := hsub _ hA0
    have e2 := hsub _ hB0
    linear_combination (PI.FglPhSplit.expMv (phAt E (add l ex (Xv 0) (Xv 1))) *
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1)))) * hcanc.symm +
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1))) * eAt E (sub l ex (Xv 0) (Xv 1)) * e1 + e2

end PI.PhiCubeOfFactor.Wk

end
