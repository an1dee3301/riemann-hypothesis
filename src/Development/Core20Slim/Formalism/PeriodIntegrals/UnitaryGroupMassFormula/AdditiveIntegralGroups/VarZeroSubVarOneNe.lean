module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.ThirdRootSubVarZeroNeZero
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DvCoeffMulEqZeroOfLtOrder
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffWSeriesVarZero
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
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

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem Gv_algHom {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (Gv W u v) = Gv W (φ u) (φ v) := by
  simp [Gv, map_add (f := _), map_mul, map_sub, map_pow, AlgHom.commutes, map_ofNat]

theorem omega_at {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0) :
    PowerSeries.subst r (omegaW W wq) * Gv W r (PowerSeries.subst r (wser wq)) = -1 := by
  have hs : PowerSeries.HasSubst r := PowerSeries.HasSubst.of_constantCoeff_zero hr
  have key := congrArg (PowerSeries.substAlgHom hs) (omega_mul_Gv h)
  rw [map_mul, Gv_algHom, map_neg, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hs] at key
  exact key

theorem root_rel {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (j : Fin 2)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0)
    (hw : PowerSeries.subst r (wser wq) = lam wq * r + nu wq)
    (hG : G W r (lam wq * r + nu wq) = 0) :
    PowerSeries.subst r (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j r *
      (3 * Acf W wq * r ^ 2 + 2 * Bcf W wq * r + Ccf W wq) =
      r * MvPowerSeries.pderiv (R := ℂ_[p]) j (lam wq) + MvPowerSeries.pderiv (R := ℂ_[p]) j (nu wq) := by
  set D := MvPowerSeries.pderiv (R := ℂ_[p]) j with hDdef
  have hω := omega_at h hr
  rw [hw] at hω
  have hD := congrArg D hG
  rw [map_zero] at hD
  simp only [G, map_add (f := _), map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_eq_mul, nsmul_eq_mul, smul_zero, zero_smul, mul_zero, zero_mul,
    add_zero, zero_add, Nat.cast_ofNat] at hD
  simp only [Gv] at hω
  simp only [Acf, Bcf, Ccf, cc]
  linear_combination (PowerSeries.subst r (omegaW W wq)) * hD -
    (r * D (lam wq) + D (nu wq)) * hω

theorem var_zero_sub_var_one_ne : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
  intro h
  have h2 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro hs
    have h3 := congrArg (fun f => f 0) hs
    simp at h3
  simp [Xv, MvPowerSeries.coeff_X, hne] at h2

theorem abel_cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  unfold flog
  simp

theorem abel {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Z3 W wq) (flog W wq) = 0 := by
  classical
  have hc0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [Xv]
  have hc1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [Xv]
  have hc2 := constantCoeff_thirdRoot W wq
  have hw0 : PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq) = lam wq * Xv 0 + nu wq := by
    show wv wq 0 = _
    simp only [nu]
    ring
  have hw1 : PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq) = lam wq * Xv 1 + nu wq :=
    wv_line1 wq
  have hw2 := subst_thirdRoot_wSeries h
  have hG0 : G W (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (lam wq * Xv 0 + nu wq) = 0 := by
    rw [← hw0]
    exact G_wv h 0
  have hG1 : G W (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (lam wq * Xv 1 + nu wq) = 0 := by
    rw [← hw1]
    exact G_wv h 1
  have hG2 := zwEquation_thirdRoot h
  have hsub : ∀ r : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff r = 0 → ∀ j,
      MvPowerSeries.pderiv (R := ℂ_[p]) j (PowerSeries.subst r (flog W wq)) =
        PowerSeries.subst r (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j r := by
    intro r hr j
    rw [pderiv_subst (PowerSeries.HasSubst.of_constantCoeff_zero hr), derivative_flog]
  have hA : Acf W wq ≠ 0 := fun h0 => by
    have h3 := constantCoeff_Acf W wq
    rw [h0, map_zero] at h3
    exact zero_ne_one h3
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro hs
    have h4 := congrArg (fun f => f 0) hs
    simp at h4
  have h01 : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := var_zero_sub_var_one_ne
  have h02 : (Xv 0 - Z3 W wq : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have h3 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
    have hBA := rt_coeff_BA W wq 0
    simp [Z3, Xv, MvPowerSeries.coeff_X, hne, hBA] at h3 <;> norm_num at h3
  have h12 : (Xv 1 - Z3 W wq : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have h3 := congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h0
    have hBA := rt_coeff_BA W wq 1
    simp [Z3, Xv, MvPowerSeries.coeff_X, hne.symm, hBA] at h3 <;> norm_num at h3
  have key : ∀ j, PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) +
      PowerSeries.subst (Z3 W wq) (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j (Z3 W wq) = 0 := by
    intro j
    have e0 := root_rel h j hc0 hw0 hG0
    have e1 := root_rel h j hc1 hw1 hG1
    have e2 := root_rel h j hc2 hw2 hG2
    have v1 := vieta1 W wq
    have v2 := vieta2 h
    set T0 := PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) with hT0
    set T1 := PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) with hT1
    set T2 := PowerSeries.subst (Z3 W wq) (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j (Z3 W wq) with hT2
    have hprod : (T0 + T1 + T2) * (Acf W wq * ((Xv 0 - Xv 1) * (Xv 0 - Z3 W wq) * (Xv 1 - Z3 W wq))) = 0 := by
      linear_combination (Xv 1 - Z3 W wq) * e0 - (Xv 0 - Z3 W wq) * e1 + (Xv 0 - Xv 1) * e2 -
        ((Xv 1 - Z3 W wq) * T0 * 2 * Xv 0 - (Xv 0 - Z3 W wq) * T1 * 2 * Xv 1 +
          (Xv 0 - Xv 1) * T2 * 2 * Z3 W wq) * v1 -
        ((Xv 1 - Z3 W wq) * T0 - (Xv 0 - Z3 W wq) * T1 + (Xv 0 - Xv 1) * T2) * v2
    rcases mul_eq_zero.1 hprod with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero hA (mul_ne_zero (mul_ne_zero h01 h02) h12))
  set F := PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Z3 W wq) (flog W wq) with hFdef
  have hF : ∀ j, MvPowerSeries.pderiv (R := ℂ_[p]) j F = 0 := fun j => by
    rw [hFdef, map_add (f := _), map_add (f := _), hsub _ hc0, hsub _ hc1, hsub _ hc2]
    exact key j
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (abel_cc_flog W wq)
  have hcc : ∀ r : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff r = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst r (flog W wq)) = 0 := by
    intro r hr
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero hr
    have hm := map_mul (PowerSeries.substAlgHom hs) PowerSeries.X g
    rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, ← hg] at hm
    rw [hm, map_mul, hr, zero_mul]
  ext e
  rw [map_zero]
  by_cases he : e = 0
  · subst he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hFdef, map_add (f := _), map_add (f := _), hcc _ hc0, hcc _ hc1,
      hcc _ hc2, add_zero, add_zero]
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 he
    have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have he' : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
    have h3 := MvPowerSeries.coeff_pderiv (i := i) F (e - Finsupp.single i 1)
    rw [hF i, map_zero, he'] at h3
    have h4 : (((e - Finsupp.single i 1 : Fin 2 →₀ ℕ) i : ℕ) : ℂ_[p]) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    exact (mul_eq_zero.1 h3.symm).resolve_right h4

end PI.AddIntG.Wk
