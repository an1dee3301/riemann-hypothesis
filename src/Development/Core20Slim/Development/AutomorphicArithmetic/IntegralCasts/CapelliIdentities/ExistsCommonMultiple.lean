module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Div.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.Qm7.exists_common_multiple.{u_2} :
    ∀ {ι : Type u_2} (s : Finset ι)
    (P : ι → ℕ → Prop),
    (∀ (i : ι) (a b : ℕ), P i a → a ∣ b → P i b) →
      (∀ i ∈ s, ∃ (a : ℕ), (0 : ℕ) < a ∧ P i a) → ∃ (d : ℕ), (0 : ℕ) < d ∧ ∀ i ∈ s, P i d := by
  intro ι s P hP h
  choose! a ha using h
  exact ⟨∏ i ∈ s, a i, Finset.prod_pos fun i hi => (ha i hi).1,
    fun i hi => hP i _ _ (ha i hi).2 (Finset.dvd_prod_of_mem a hi)⟩
