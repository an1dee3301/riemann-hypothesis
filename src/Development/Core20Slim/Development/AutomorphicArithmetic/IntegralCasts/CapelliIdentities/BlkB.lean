module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Notation

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Yha8.blkA :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ {i : Fin n | (↑i : ℕ) < j}

noncomputable def UpperTheory.Reformulated.B.Yha8.blkB :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ (UpperTheory.Reformulated.B.Yha8.blkA j)ᶜ

theorem UpperTheory.Reformulated.B.Yha8.main :
    ∀ {n : ℕ} (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ),
      (∀ (a b : Fin n), Q a b ≠ (0 : ℂ) → b ∈ UpperTheory.Reformulated.B.Yha8.blkA j) →
        (∀ (a b : Fin n), S a b ≠ (0 : ℂ) → a ∈ UpperTheory.Reformulated.B.Yha8.blkB j) → Q * S = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  intro n j Q S hQ hS
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hq : Q a b = 0
  · simp [hq]
  by_cases hs : S b c = 0
  · simp [hs]
  exfalso
  have h1 := hQ a b hq
  have h2 := hS b c hs
  unfold UpperTheory.Reformulated.B.Yha8.blkB at h2
  rw [Finset.mem_compl] at h2
  exact h2 h1
