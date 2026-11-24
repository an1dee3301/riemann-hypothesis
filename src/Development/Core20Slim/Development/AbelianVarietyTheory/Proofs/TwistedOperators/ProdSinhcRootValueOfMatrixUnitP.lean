module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU.RootProd

theorem shc_neg' (x : ℝ) : shc (-x) = shc x := by
  unfold shc
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]

theorem shc_zero' : shc 0 = 1 := by
  unfold shc
  exact if_pos rfl

theorem prod_square (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, F i j =
      (∏ i ∈ Finset.range n, F i i) *
        ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F i j * F j i else 1 := by

  have split3 : ∀ i j, F i j = (if j = i then F i i else 1) * (if i < j then F i j else 1) *
      (if j < i then F i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.ne', not_lt.mpr hij.le]
    · simp
    · simp [hji, hji.ne, not_lt.mpr hji.le]
  have row : ∀ i ∈ Finset.range n, (∏ j ∈ Finset.range n, F i j) =
      F i i * ((∏ j ∈ Finset.range n, if i < j then F i j else 1) *
        ∏ j ∈ Finset.range n, if j < i then F i j else 1) := by
    intro i hi
    have hd : (∏ j ∈ Finset.range n, if j = i then F i i else 1) = F i i := by
      rw [Finset.prod_ite_eq']
      exact if_pos hi
    rw [← Finset.prod_mul_distrib, ← hd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_assoc]; exact split3 i j

  have below : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if j < i then F i j else 1) =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F j i else 1 :=
    Finset.prod_comm
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib, Finset.prod_mul_distrib, below,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem prod_PIx (p q : ℕ) (h : ℕ → ℝ) :
    ∏ ab : PIx p q, shc (rootP h ab.1) =
      ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range q,
        shc (cutH p q h i - cutH p q h j) * shc (cutH p q h i + cutH p q h j) := by

  rw [← Finset.prod_subtype (Finset.univ.filter fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2)
    (fun ab => by simp) (fun ab => shc (rootP h ab))]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, sameBlock, not_true_eq_false, not_false_eq_true, if_false,
    if_true, Finset.prod_const_one, one_mul, mul_one, rootP, Sum.isLeft_inl, Sum.isLeft_inr,
    posIx, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true]
  simp_rw [Finset.prod_range, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [add_comm]

theorem prod_rect (m d : ℕ) (h c : ℕ → ℝ) (hc : ∀ n, c n = if n < m then h n else 0) :
    ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j) =
      (∏ i ∈ Finset.range m, shc (2 * h i) * shc (h i) ^ (2 * d)) *
        ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
          if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  have hin : ∀ i ∈ Finset.range m, c i = h i := fun i hi => by
    rw [hc, if_pos (Finset.mem_range.mp hi)]
  have hout : ∀ k, c (m + k) = 0 := fun k => by
    rw [hc, if_neg (by omega)]

  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]

  have row : ∀ i ∈ Finset.range m,
      (∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j)) =
        (∏ j ∈ Finset.range m, shc (h i - h j) * shc (h i + h j)) * shc (h i) ^ (2 * d) := by
    intro i hi
    rw [Finset.prod_range_add]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [hin i hi, hin j hj]
    · simp only [hout, hin i hi, sub_zero, add_zero]
      rw [Finset.prod_const, Finset.card_range, ← pow_two, ← pow_mul]
  have diag : ∀ i, shc (h i - h i) * shc (h i + h i) = shc (2 * h i) := fun i => by
    rw [sub_self, shc_zero', one_mul, two_mul]
  have off : ∀ i j, (if i < j then shc (h i - h j) * shc (h i + h j) * (shc (h j - h i) * shc (h j + h i))
      else 1) = if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := fun i j => by
    rw [swap (h i) (h j), sq]
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib,
    prod_square m (fun i j => shc (h i - h j) * shc (h i + h j))]
  simp only [diag]
  rw [Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => off i j]
  ring

theorem prod_shc_rootP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  intro p q h
  have hm : min p q + (max p q - min p q) = max p q := Nat.add_sub_cancel' min_le_max
  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]
  rw [← prod_rect (min p q) (max p q - min p q) h (cutH p q h) (fun n => rfl), hm, prod_PIx]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  ·
    rw [min_eq_right hqp, max_eq_left hqp, Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => swap _ _

end GlobalTheory.PolarU.RootProd
