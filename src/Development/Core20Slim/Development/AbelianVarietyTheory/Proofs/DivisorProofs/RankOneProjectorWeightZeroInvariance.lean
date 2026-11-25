module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

namespace RankOnePf

variable {W : Type} [AddCommGroup W] [Module ℚ W]

theorem rankOne_H_X_pow (X H : Module.End ℚ W) (hHX : ∀ w, H (X w) = X (H w) + (2 : ℚ) • X w)
    (k : ℕ) (w : W) : H ((X ^ k) w) = (X ^ k) (H w) + ((2 * k : ℕ) : ℚ) • (X ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHX, map_add (f := _), map_smul]
    push_cast
    module

theorem rankOne_H_Y_pow (Y H : Module.End ℚ W) (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w)
    (k : ℕ) (w : W) : H ((Y ^ k) w) = (Y ^ k) (H w) - ((2 * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHY, map_sub, map_smul]
    push_cast
    module

theorem rankOne_X_Y_pow (X Y H : Module.End ℚ W) (hXY : ∀ w, X (Y w) = Y (X w) + H w)
    (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w) (k : ℕ) (w : W) :
    X ((Y ^ (k + 1)) w) = (Y ^ (k + 1)) (X w) + ((k + 1 : ℕ) : ℚ) • (Y ^ k) (H w)
      - (((k + 1) * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp [hXY]
  | succ k ih =>
    have h1 : (Y ^ (k + 1 + 1)) w = (Y ^ (k + 1)) (Y w) := by
      rw [pow_succ Y (k + 1), Module.End.mul_apply]
    rw [h1, ih, hXY, hHY]
    simp only [map_add (f := _), map_sub, map_smul, pow_succ, Module.End.mul_apply]
    push_cast
    module

theorem rankOne_coef_succ (n : ℕ) :
    coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ) = - coef 0 n := by
  have h1 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [coef, Nat.factorial_succ, add_zero, Nat.factorial_zero]
  push_cast
  field_simp
  ring

end RankOnePf

end GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut


open RankOnePf in
theorem rankOne : RankOne := by
  intro W _ _ N K D hG hB o q ho hq hoq T hoT hqT
  have hqo : q ≠ o := Ne.symm hoq
  have hH : ∀ x, (D o o - D q q) x = D o o x - D q q x := fun x => rfl
  have hHT : (D o o - D q q) T = 0 := by rw [hH, hoT, hqT, sub_zero]
  have hXY : ∀ w, D o q (D q o w) = D q o (D o q w) + (D o o - D q q) w := by
    intro w
    have e := LinearMap.congr_fun (hG o q q o ho hq hq ho) w
    rw [if_pos (rfl : q = q), if_pos (rfl : o = o)] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    rw [hH]
    exact sub_eq_iff_eq_add'.mp e
  have hHX : ∀ w, (D o o - D q q) (D o q w) = D o q ((D o o - D q q) w) + (2 : ℚ) • D o q w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o o q ho ho ho hq) w
    rw [if_pos (rfl : o = o), if_neg hqo] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e1
    have e2 := LinearMap.congr_fun (hG q q o q hq hq ho hq) w
    rw [if_neg hqo, if_pos (rfl : q = q)] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  have hHY : ∀ w, (D o o - D q q) (D q o w) = D q o ((D o o - D q q) w) - (2 : ℚ) • D q o w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o q o ho ho hq ho) w
    rw [if_neg hoq, if_pos (rfl : o = o)] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e1
    have e2 := LinearMap.congr_fun (hG q q q o hq hq hq ho) w
    rw [if_pos (rfl : q = q), if_neg hoq] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  constructor
  ·
    have hterm : ∀ m : ℕ, D o q ((D q o ^ (m + 1)) ((D o q ^ (m + 1)) T)) =
        (D q o ^ (m + 1)) ((D o q ^ (m + 1 + 1)) T) +
          (((m + 1) * (m + 1 + 1) : ℕ) : ℚ) • (D q o ^ m) ((D o q ^ (m + 1)) T) := by
      intro m
      have hx : D o q ((D o q ^ (m + 1)) T) = (D o q ^ (m + 1 + 1)) T := by
        rw [pow_succ' (D o q) (m + 1), Module.End.mul_apply]
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, rankOne_H_X_pow _ _ hHX, hHT, map_zero, zero_add, hx,
        map_smul]
      push_cast
      module
    have hsum : ∀ n : ℕ, D o q (∑ k ∈ Finset.range (n + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T)) =
        coef 0 n • (D q o ^ n) ((D o q ^ (n + 1)) T) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add (f := _), ih, map_smul, hterm n]
        have hc := rankOne_coef_succ n
        rw [show coef 0 n = -(coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ)) by rw [hc, neg_neg]]
        module
    have hXK : (D o q ^ (K + 1)) T = 0 := by
      refine hB o ho q hq ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_X_pow _ _ hHX (K + 1) T
      rw [hHT, map_zero, zero_add, hH] at h
      rw [Int.cast_natCast]
      exact h
    have hp : proj K 0 (D o q) (D q o) T =
        ∑ k ∈ Finset.range (K + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T) := by
      simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [hp, hsum K, hXK, map_zero, smul_zero]
  ·
    intro hXT
    have hYterm : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) T) = -((((k + 1) * k : ℕ) : ℚ)) • (D q o ^ k) T := by
      intro k
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, hXT, hHT, map_zero, map_zero, smul_zero, add_zero, zero_sub,
        neg_smul]
    have hYK : (D q o ^ (K + 1)) T = 0 := by
      refine hB q hq o ho ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_Y_pow _ _ hHY (K + 1) T
      rw [hHT, map_zero, zero_sub, hH] at h
      rw [Int.cast_natCast, ← neg_sub, h, neg_neg]
    have hdesc : ∀ d i : ℕ, i + d = K → (D q o ^ (i + 1)) T = 0 := by
      intro d
      induction d with
      | zero =>
        intro i hi
        rw [add_zero] at hi
        subst hi
        exact hYK
      | succ d ih =>
        intro i hi
        have h2 := ih (i + 1) (by omega)
        have h3 := hYterm (i + 1)
        rw [h2, map_zero] at h3
        rcases smul_eq_zero.mp h3.symm with h | h
        · exfalso
          have : ((((i + 1 + 1) * (i + 1) : ℕ) : ℚ)) ≠ 0 := by positivity
          exact this (neg_eq_zero.mp h)
        · exact h
    have := hdesc K 0 (by omega)
    simpa using this

end GlobalTheory.LeviCut
