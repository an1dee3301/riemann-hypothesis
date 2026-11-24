module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAddOfLt
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic

@[expose] public section

namespace GlobalTheory.TorsionIntegral

open IsUltrametricDist WeierstrassCurve

variable {K : Type} [NormedField K] [IsUltrametricDist K]


lemma norm_add_eq_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖x‖ < ‖x‖ ^ 3 := by
    have := pow_lt_pow_right₀ hx (show 1 < 3 by norm_num)
    simpa using this
  rw [← norm_pow, h, add_assoc, norm_add_eq_of_lt, norm_pow]
  rw [norm_pow]
  refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by linarith))
  rw [norm_mul]
  nlinarith [norm_nonneg A]




noncomputable def param {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x y _ => x / y

def Near {W : Affine K} (M : ℝ) : W.Point → Prop
  | .zero => True
  | .some x _ _ => M ≤ ‖x‖

lemma add_step [DecidableEq K] {A B : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (P Q : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  first
  | exact @_root_.GlobalTheory.UltrametricLineBounds.large_add
  | exact _root_.GlobalTheory.UltrametricLineBounds.large_add
  | (apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricLineBounds.large_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricLineBounds.large_add ..)

theorem norm_x_le_one_of_nsmul_eq_zero (K : Type) [NormedField K] [IsUltrametricDist K]
    [DecidableEq K] (A B : K) (N : ℕ) (x y : K)
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  have M0 : 0 ≤ ‖x‖⁻¹ := by positivity
  have hP : Near ‖x‖ (Affine.Point.some x y h) := le_refl _
  have key : ∀ k : ℕ, Near ‖x‖ (k • Affine.Point.some x y h) ∧
      ‖param (k • Affine.Point.some x y h) - (k : K) * (x / y)‖ ≤ ‖x‖⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [zero_nsmul]
      exact ⟨trivial, by simp [Affine.Point.zero_def, param]⟩
    | succ k ih =>
      obtain ⟨s1, s2⟩ := add_step hA hB hx _ _ ih.1 hP
      rw [succ_nsmul]
      refine ⟨s1, ?_⟩
      have := (norm_add_le_max _ _).trans (max_le s2 ih.2)
      refine le_of_eq_of_le (congrArg norm ?_) this
      simp only [param]
      push_cast
      ring
  have h1 := (key N).2
  rw [h0] at h1
  simp only [Affine.Point.zero_def, param, zero_sub, norm_neg, norm_mul, hN, one_mul,
    norm_div] at h1
  have he : y ^ 2 = x ^ 3 + A * x + B := by
    have := (Affine.equation_iff _ _).1 h.1
    simp only at this
    linear_combination this
  have hy := norm_y_sq hA hB hx he
  have x0 : 0 < ‖x‖ := by linarith
  have y0 : 0 < ‖y‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hy
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ y0 x0, one_mul] at h1
  have h2 : (‖x‖ * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [hy] at h2
  have : ‖x‖ ^ 3 * 1 < ‖x‖ ^ 3 * ‖x‖ := by gcongr
  nlinarith

end GlobalTheory.TorsionIntegral
