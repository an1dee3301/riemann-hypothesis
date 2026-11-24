module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PI.FglShared

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem l_constantCoeff {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h := constantCoeff_subst_of_zero (a := ex) hex0 l
  rw [hinv] at h
  rw [← h]
  exact PowerSeries.constantCoeff_X

theorem subst_subst_eq {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) : PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hinv, PowerSeries.subst_X hy']

theorem l_ne_zero {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : l ≠ 0 := by
  rintro rfl
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  rw [← PowerSeries.coe_substAlgHom hex, map_zero] at hinv
  exact PowerSeries.X_ne_zero hinv.symm

theorem exists_coeff_ne {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : ∃ k, k ≠ 0 ∧ PowerSeries.coeff k l ≠ 0 := by
  have hl0 := l_constantCoeff hex0 hinv
  by_contra hc
  push Not at hc
  apply l_ne_zero hex0 hinv
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hl0
  · simpa using hc k hk

theorem subst_ne_zero {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) (hne : y ≠ 0) : PowerSeries.subst y ex ≠ 0 := by
  intro h0
  have h := subst_subst_eq hex0 hinv hy
  rw [h0, PowerSeries.subst_zero_of_constantCoeff_zero (l_constantCoeff hex0 hinv)] at h
  exact hne h.symm

theorem coeff_single_lg {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) {k : ℕ}
    (hk : k ≠ 0) : coeff (Finsupp.single i k) (PowerSeries.subst (X j : MvPowerSeries σ ℂ_[p]) l) =
      if j = i then PowerSeries.coeff k l else 0 := by
  rw [PowerSeries.coeff_subst_single]
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : Finsupp.single i k ≠ Finsupp.single j ((Finsupp.single i k) j) := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hji), Finsupp.single_zero]
      exact Finsupp.single_ne_zero.mpr hk
    rw [if_neg hne, if_neg hji]

end PI.FglShared

end
