module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory

theorem hermite_reduction_column {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R → R) (hb : ∀ i j, j < i → b i j = 0) (hr : ∀ i y, b i i ∣ y - r i y)
    (j : Fin n) (m : ℕ) :
    ∃ x : Fin n → R, x j = 1 ∧ (∀ l, j < l → x l = 0) ∧
      ∀ i : Fin n, i < j → (j : ℕ) ≤ i + m → ∃ y, b.mulVec x i = r i y := by
  induction m with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩
    exact absurd (Fin.lt_def.1 hi) (by omega)
  | succ m ih =>
    obtain ⟨x, hx1, hx0, hx⟩ := ih
    by_cases h : ∃ k : Fin n, (j : ℕ) = k + m + 1
    · obtain ⟨k, hk⟩ := h
      obtain ⟨z, hz⟩ := hr k (b.mulVec x k)
      have hkj : k < j := Fin.lt_def.2 (by omega)
      have key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z := by
        intro i
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      refine ⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩
      · simp [hx1, hkj.ne']
      · simp [hx0 l hl, (hkj.trans hl).ne']
      · rw [key]
        by_cases hik : i = k
        · subst hik
          exact ⟨b.mulVec x i, by rw [← hz]; ring⟩
        · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
          have hki : k < i := Fin.lt_def.2 (by omega)
          rw [hb i k hki, zero_mul, sub_zero]
          exact hx i hi (by omega)
    · refine ⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩
      by_contra hc
      exact h ⟨i, by omega⟩

theorem hermite_reduction_unipotent :
    ∀ (R : Type) [CommRing R] (n : ℕ) (b : Matrix (Fin n) (Fin n) R) (r : Fin n → R → R),
      (∀ i j, j < i → b i j = 0) → (∀ i y, b i i ∣ y - r i y) →
      ∃ u : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        ∀ i j, i < j → ∃ y, (b * u) i j = r i y := by
  intro R _ n b r hb hr
  choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n
  refine ⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩
  obtain ⟨y, hy⟩ := hx j i h (by have := j.2; omega)
  exact ⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩

end GlobalTheory
