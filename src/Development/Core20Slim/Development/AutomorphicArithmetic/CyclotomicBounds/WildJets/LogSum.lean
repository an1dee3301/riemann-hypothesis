module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

theorem UpperTheory.WildA.logSum :
    ∀ y : ℝ, 1 ≤ y → ∑ l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.logb l y * Real.log l ≤ y * Real.log y := by
  intro y hy
  set S := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime with hS
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ l ∈ S, Real.logb l y * Real.log l = Real.log y := by
    intro l hl
    have hp : Nat.Prime l := (Finset.mem_filter.1 hl).2
    have h1 : (1:ℝ) < l := by exact_mod_cast hp.one_lt
    have hlog : Real.log l ≠ 0 := (Real.log_pos h1).ne'
    rw [Real.logb, div_mul_cancel₀ _ hlog]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hlogy
  have hsub : S ⊆ (Finset.range (⌊y⌋₊ + 1)).erase 0 := by
    intro l hl
    rw [hS, Finset.mem_filter] at hl
    exact Finset.mem_erase.2 ⟨hl.2.ne_zero, hl.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at hcard
  have h2 : S.card ≤ ⌊y⌋₊ := by omega
  calc (S.card : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
    _ ≤ y := Nat.floor_le (by linarith)
