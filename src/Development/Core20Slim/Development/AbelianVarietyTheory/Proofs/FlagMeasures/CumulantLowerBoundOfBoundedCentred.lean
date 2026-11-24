module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpQuadraticLowerAndLogLinearLowerStatement
public import Batteries.Logic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix Finset Real

namespace GlobalTheory

theorem cumulant_lower_bound_of_bounded_centred :
    ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 →
      ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) →
      min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  intro ι _ w y R hR hw hs hm hb
  obtain ⟨hexp, hlog⟩ := GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower'
  set t : ℝ := min 1 (1 / R) with ht
  set V : ℝ := ∑ J, w J * y J ^ 2 with hV
  set S : ℝ := ∑ J, w J * Real.exp (y J) with hS
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R ≤ 1 := by
    have : t ≤ 1 / R := min_le_right _ _
    rwa [le_div_iff₀ hR] at this
  have hty : ∀ J, w J ≠ 0 → |t * y J| ≤ 1 := by
    intro J hJ
    rw [abs_mul, abs_of_pos ht0]
    exact (mul_le_mul_of_nonneg_left (hb J hJ) ht0.le).trans htR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun J _ => mul_nonneg (hw J) (sq_nonneg _)
  have htV : t ^ 2 * V ≤ 1 := by
    rw [hV, Finset.mul_sum, ← hs]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · have h1 : (t * y J) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hty J hJ)
      have := mul_le_mul_of_nonneg_left h1 (hw J)
      nlinarith
  have hlow : 1 + t ^ 2 * V / 3 ≤ ∑ J, w J * Real.exp (t * y J) := by
    have e : 1 + t ^ 2 * V / 3 = ∑ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3) := by
      have e2 : ∀ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3)
          = w J + t * (w J * y J) + t ^ 2 / 3 * (w J * y J ^ 2) := fun J => by ring
      simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hm]
      rw [← hV]; ring
    rw [e]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · exact mul_le_mul_of_nonneg_left (hexp _ (hty J hJ)) (hw J)
  have hS1 : 1 ≤ S := by
    have : ∑ J, w J * (y J + 1) = 1 := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hs, hm, zero_add]
    rw [← this]
    exact Finset.sum_le_sum fun J _ =>
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hw J)
  have hS0 : 0 < S := by linarith
  set F : ℝ := Real.log S with hF
  have hEF : Real.exp F = S := Real.exp_log hS0
  have hpt : ∀ J, Real.exp (t * y J)
      ≤ Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t)) := by
    intro J
    have h := convexOn_exp.2 (Set.mem_univ (y J - F)) (Set.mem_univ 0) ht0.le
      (sub_nonneg.2 ht1) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
    rw [Real.exp_sub, hEF] at h
    have e : t * y J = t * F + t * (y J - F) := by ring
    rw [e, Real.exp_add]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hup : ∑ J, w J * Real.exp (t * y J) ≤ Real.exp (t * F) := by
    calc ∑ J, w J * Real.exp (t * y J)
        ≤ ∑ J, w J * (Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t))) :=
          Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hpt J) (hw J)
      _ = ∑ J, (Real.exp (t * F) * t / S * (w J * Real.exp (y J))
            + Real.exp (t * F) * (1 - t) * w J) :=
          Finset.sum_congr rfl fun J _ => by ring
      _ = Real.exp (t * F) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hS]
          field_simp
          ring
  have hu0 : 0 ≤ t ^ 2 * V / 3 := by positivity
  have h1 := hlog (t ^ 2 * V / 3) hu0 (by linarith)
  have h2 : Real.log (1 + t ^ 2 * V / 3) ≤ t * F := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hlow.trans hup
  have h3 : t * (t * V / 4) ≤ t * F := by nlinarith
  exact le_of_mul_le_mul_left h3 ht0

end GlobalTheory
