module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.AreaLat
public import Development.Core20Slim.Formalism.PeriodIntegrals.LatDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace PI.AreaLatWork

open PI

lemma im_conj_mul_combo (w₁ w₂ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im
      = ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
  simp only [zsmul_eq_mul, map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

lemma im_integral (w₁ w₂ : ℂ) :
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂,
      ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im := by
  intro a ha b hb
  obtain ⟨m, n, rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp ha
  obtain ⟨m', n', rfl⟩ := (AddSubgroup.mem_closure_pair (x := w₁) (y := w₂)).mp hb
  exact ⟨m * n' - n * m', im_conj_mul_combo w₁ w₂ m n m' n'⟩

theorem areaLat : PI.AreaLat := by
  intro w₁ w₂ hne
  refine ⟨?_, im_integral w₁ w₂⟩
  unfold PI.area
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨abs_pos.mpr hne, w₁, ?_, w₂, ?_, rfl⟩
    · exact AddSubgroup.subset_closure (Set.mem_insert _ _)
    · exact AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rintro a ⟨ha, x, hx, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := im_integral w₁ w₂ x hx y hy
    rw [hn, abs_mul] at ha ⊢
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul] at ha
      exact lt_irrefl _ ha
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hn0)
    have h2 := mul_le_mul_of_nonneg_right hn1 (abs_nonneg (((starRingEnd ℂ) w₁ * w₂).im))
    linarith

end PI.AreaLatWork
