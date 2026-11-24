module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem twelve_dvd_five_pow_three_add_seven_pow_five (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * d ^ 3 + 7 * d ^ 5) 12).mp
    (by push_cast; exact key _)
  exact_mod_cast h

theorem sigma_congr (n : ℕ) :
    (12 : ℤ) ∣ 5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_pow_three_add_seven_pow_five _

def s3Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 3 n : ℤ)

def s5Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 5 n : ℤ)

def tZ : PowerSeries ℤ := PowerSeries.mk fun n =>
  (5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ)) / 12

theorem eisensteinFourInt_eq : e4Z = 1 + PowerSeries.C (240 : ℤ) * s3Z := by
  ext n
  simp only [e4Z, s3Z, map_add (f := _), PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem eisensteinSixInt_eq : e6Z = 1 - PowerSeries.C (504 : ℤ) * s5Z := by
  ext n
  simp only [e6Z, s5Z, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem tZ_mul : PowerSeries.C (12 : ℤ) * tZ =
    PowerSeries.C (5 : ℤ) * s3Z + PowerSeries.C (7 : ℤ) * s5Z := by
  ext n
  simp only [map_add (f := _), PowerSeries.coeff_C_mul, tZ, s3Z, s5Z, PowerSeries.coeff_mk]
  exact Int.mul_ediv_cancel' (sigma_congr n)

theorem eisenstein_cube_sub_sq_eq : e4Z ^ 3 - e6Z ^ 2 = PowerSeries.C (1728 : ℤ) *
    (tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 + PowerSeries.C (8000 : ℤ) * s3Z ^ 3
      - PowerSeries.C (147 : ℤ) * s5Z ^ 2) := by
  have h := tZ_mul
  rw [eisensteinFourInt_eq, eisensteinSixInt_eq]
  simp only [map_ofNat] at h ⊢
  linear_combination (-144 : PowerSeries ℤ) * h

theorem dZ_mul : PowerSeries.C (1728 : ℤ) * dZ = e4Z ^ 3 - e6Z ^ 2 := by
  ext n
  rw [PowerSeries.coeff_C_mul, dZ, PowerSeries.coeff_mk, eisenstein_cube_sub_sq_eq, PowerSeries.coeff_C_mul]
  exact Int.mul_ediv_cancel' (dvd_mul_right _ _)

private theorem dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq : dZ = tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 +
    PowerSeries.C (8000 : ℤ) * s3Z ^ 3 - PowerSeries.C (147 : ℤ) * s5Z ^ 2 := by
  have h := dZ_mul.trans eisenstein_cube_sub_sq_eq
  refine mul_left_cancel₀ (fun h0 => ?_) h
  have := congrArg PowerSeries.constantCoeff h0
  rw [PowerSeries.constantCoeff_C, map_zero] at this
  norm_num at this

theorem dZ_coeff_zero : PowerSeries.coeff 0 dZ = 0 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add (f := _), PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dZ_coeff_one : PowerSeries.coeff 1 dZ = 1 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add (f := _), PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dC_eq : dC = qExpansion 1 DD := by
  have h4 : qExpansion 1 ⇑((E₄.mul E₄).mul E₄) = qExpansion 1 E₄ ^ 3 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp), ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have h6 : qExpansion 1 ⇑(E₆.mul E₆) = qExpansion 1 E₆ ^ 2 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have hfun : DD = ⇑((1 / 1728 : ℂ) • ((E₄.mul E₄).mul E₄)) - ⇑((1 / 1728 : ℂ) • (E₆.mul E₆)) := by
    funext τ
    simp only [DD, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, Pi.sub_apply,
      ModularForm.coe_smul, ModularForm.coe_mul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hd := congrArg (PowerSeries.map (Int.castRingHom ℂ)) dZ_mul
  rw [map_mul, map_sub, map_pow, map_pow, PowerSeries.map_C, map_eisensteinFourInt, map_eisensteinSixInt] at hd
  rw [hfun, ModularForm.qExpansion_sub one_pos (by simp), ModularForm.coe_smul, ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos (by simp), ModularForm.qExpansion_smul one_pos (by simp),
    h4, h6, ← smul_sub, ← hd, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  rw [show (1 / 1728 : ℂ) * (Int.castRingHom ℂ) 1728 = 1 by norm_num, map_one, one_mul]
  rfl

end ReciprocityTheory.ChartRestriction.L1
