module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.CancelDenoms.Core
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
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace GlobalTheory.UnitNormRealPartBound

lemma norm_eq_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) : ‖z‖ = 1 := by
  have hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2 := fun n => by
    have := h n
    calc ‖z‖ ^ n = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel, norm_pow]
      _ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 3 / 2 := by rw [norm_one]; linarith
  have hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n := fun n => by
    have := h n
    have h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖ := by
      calc ‖(1 : ℂ)‖ = ‖-(z ^ n - 1) + z ^ n‖ := by ring_nf
        _ ≤ ‖-(z ^ n - 1)‖ + ‖z ^ n‖ := norm_add_le _ _
        _ = ‖z ^ n - 1‖ + ‖z ^ n‖ := by rw [norm_neg]
    rw [norm_one, norm_pow] at h2
    linarith
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith [hlo n]
  · exact h1
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) h1
    linarith [hup n]

lemma re_gt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have hz := norm_eq_one h
  have hnp : ∀ n : ℕ, ‖z ^ n‖ = 1 := fun n => by rw [norm_pow, hz, one_pow]
  have hre : ∀ n : ℕ, 7 / 8 < (z ^ n).re := fun n => re_gt (hnp n) (h n)
  have key : ∀ k : ℕ, (7 / 4 : ℝ) ^ k * |z.im| ≤ |(z ^ (2 ^ k)).im| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k) := by
        rw [pow_succ, pow_mul, sq]
      have hr := hre (2 ^ k)
      have e2 : (z ^ (2 ^ (k + 1))).im = 2 * (z ^ (2 ^ k)).re * (z ^ (2 ^ k)).im := by
        rw [e, Complex.mul_im]; ring
      rw [e2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * (z ^ 2 ^ k).re), pow_succ]
      have : (7 / 4 : ℝ) ≤ 2 * (z ^ 2 ^ k).re := by linarith
      have hn : 0 ≤ (7 / 4 : ℝ) ^ k * |z.im| := by positivity
      nlinarith [abs_nonneg (z ^ 2 ^ k).im]
  have him : z.im = 0 := by
    by_contra hne
    have hpos : 0 < |z.im| := abs_pos.mpr hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / |z.im|) (by norm_num : (1 : ℝ) < 7 / 4)
    have hb : |(z ^ (2 ^ k)).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hnp _).le
    have : 1 < (7 / 4 : ℝ) ^ k * |z.im| := by rwa [div_lt_iff₀ hpos] at hk
    linarith [key k]
  have h1 := hre 1
  rw [pow_one] at h1
  have h2 : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him] at h2
  apply Complex.ext
  · simp; nlinarith
  · simp [him]

end GlobalTheory.UnitNormRealPartBound
