module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FlowLemma

open MvPolynomial in
private lemma shiftNu_add_right {p q : ℕ} (c : ℚ) (f g : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (a : _root_.Formalism.BasicNotions.TH.Ix p q) :
    _root_.Formalism.BasicNotions.TH.shiftNu c (fun x => f x + g x) a = _root_.Formalism.BasicNotions.TH.shiftNu c f a + g a := by
  cases a <;> simp only [_root_.Formalism.BasicNotions.TH.shiftNu] <;> ring

open MvPolynomial in
private lemma degW_blattner_le_of_sign_lemma {p q : ℕ} (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c : ℚ) (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam) (s : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (hs : ∀ a, s a = 1 ∨ s a = -1)
    (hsν : ∀ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a = |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|)
    (hmono : ∀ a b, lam b < lam a → s b ≤ s a)
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  obtain ⟨m, hm, rfl⟩ := hC μ v hv
  set Δ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ := fun x =>
    ∑ a, ∑ b, (m a b : ℚ) * ((if x = a then 1 else 0) - if x = b then 1 else 0) with hΔ
  have key : ∑ x, s x * Δ x = ∑ a, ∑ b, (m a b : ℚ) * (s a - s b) := by
    simp only [hΔ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hnn : 0 ≤ ∑ x, s x * Δ x := by
    rw [key]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : m a b = 0
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hmono a b (hm a b h0)))
  have habs : ∀ x y : ℚ, ∀ a, s a * (x + y) ≤ |x + y| := by
    intro x y a
    rcases hs a with h | h <;> rw [h]
    · simpa using le_abs_self (x + y)
    · simpa using neg_le_abs (x + y)
  unfold _root_.Formalism.BasicNotions.TH.degW
  calc ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|
      = ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a := by simp [hsν]
    _ ≤ ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + ∑ x, s x * Δ x := le_add_of_nonneg_right hnn
    _ = ∑ a, s a * (_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a) := by
        rw [← Finset.sum_add_distrib]; simp [mul_add]
    _ ≤ ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a| :=
        Finset.sum_le_sum fun a _ => habs _ _ a
    _ = ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (fun x => _root_.Formalism.BasicNotions.TH.blattner lam x + Δ x) a| := by
        simp [shiftNu_add_right]


open MvPolynomial in
theorem _root_.GlobalTheory.FlowLemma.degW_blattner_le (p q : ℕ) (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c θ : ℚ)
    (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam)
    (hs : ∀ a, (θ < lam a → 0 ≤ _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a) ∧
      (lam a ≤ θ → _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a ≤ 0))
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  refine degW_blattner_le_of_sign_lemma M lam c hC (fun a => if θ < lam a then 1 else -1)
    (fun a => ?_) (fun a => ?_) (fun a b hab => ?_) μ v hv
  · split_ifs <;> simp
  · split_ifs with h
    · simp [abs_of_nonneg ((hs a).1 h)]
    · simp [abs_of_nonpos ((hs a).2 (not_lt.1 h))]
  · beta_reduce
    split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num

end GlobalTheory.FlowLemma
