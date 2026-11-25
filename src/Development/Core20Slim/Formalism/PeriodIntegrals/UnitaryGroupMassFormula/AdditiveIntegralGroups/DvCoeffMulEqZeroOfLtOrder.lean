module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine
public import Batteries.Logic
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
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
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Tactic.FieldSimp.Lemmas
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

theorem dv_exists_lt_order_pow {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (N : ℕ) : ∃ m : ℕ, (N : ℕ∞) < (a ^ m).order := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨k * (N + 1), ?_⟩
  have h0 : MvPowerSeries.constantCoeff (a ^ k) = 0 := by rw [map_pow]; exact hk
  have := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (N + 1) h0
  rw [← pow_mul] at this
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) this

theorem dv_coeff_mul_eq_zero_of_lt_order {R : Type*} [CommRing R] {σ : Type*} (f g : MvPowerSeries σ R)
    (e : σ →₀ ℕ) (h : (e.degree : ℕ∞) < f.order) : MvPowerSeries.coeff e (f * g) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le h (le_trans le_self_add MvPowerSeries.le_order_mul)

theorem dv_pderiv_subst_coe {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (P : Polynomial R) (i : σ) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a (P : PowerSeries R)) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) (P : PowerSeries R)) * MvPowerSeries.pderiv (R := R) i a := by
  rw [PowerSeries.derivative_coe, PowerSeries.subst_coe ha, PowerSeries.subst_coe ha,
    Derivation.comp_aeval_eq, smul_eq_mul]

theorem pderiv_subst {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) (i : σ) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) f) * MvPowerSeries.pderiv (R := R) i a := by
  rw [← sub_eq_zero]
  ext e
  rw [map_zero]
  obtain ⟨m, hm⟩ := dv_exists_lt_order_pow ha e.degree
  set g : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + m) f
  have hf : f = ((PowerSeries.trunc m f : Polynomial R) : PowerSeries R) + PowerSeries.X ^ m * g := by
    ext n
    rw [map_add (f := _), Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul']
    by_cases hn : n < m
    · simp [hn, not_le.mpr hn]
    · simp [hn, not_lt.mp hn, g, Nat.sub_add_cancel (not_lt.mp hn)]
  have key : MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a f) -
      PowerSeries.subst a (PowerSeries.derivative (R := R) f) * MvPowerSeries.pderiv (R := R) i a =
      a ^ m * (MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a g) -
        PowerSeries.subst a (PowerSeries.derivative (R := R) g) * MvPowerSeries.pderiv (R := R) i a) := by
    have hc : PowerSeries.subst a ((m : PowerSeries R)) = (m : MvPowerSeries σ R) := by
      rw [← map_natCast (PowerSeries.C (R := R)), PowerSeries.subst_C, map_natCast]
    conv_lhs => rw [hf]
    simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      PowerSeries.derivative_X, mul_one]
    simp only [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha,
      PowerSeries.subst_X ha, hc]
    simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      dv_pderiv_subst_coe ha]
    ring
  rw [key]
  exact dv_coeff_mul_eq_zero_of_lt_order _ _ e hm

theorem derivative_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.derivative (R := ℂ_[p]) (flog W wq) = omegaW W wq := by
  ext n
  rw [PowerSeries.coeff_derivative, flog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n),
    Nat.add_sub_cancel]
  have h : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

end PI.AddIntG.Wk
