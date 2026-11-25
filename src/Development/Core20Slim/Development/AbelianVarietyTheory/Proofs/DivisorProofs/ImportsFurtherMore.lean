module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

universe u_1 u_2

namespace GlobalTheory.BandLemmaThird

theorem main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [inst_1 : Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {i j : ℕ} {X Y : Matrix ι ι k}, d1 ℓ i X → d1 ℓ j Y → d1 ℓ (i + j) (X * Y)) := by
  intro d1 k _ ι _ _ ℓ i j X Y hX hY r s hrs
  show (X * Y) r s = 0
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases h : ℓ t < ℓ r + i
  · rw [hX r t h, zero_mul]
  · rw [hY t s (by omega), mul_zero]

end GlobalTheory.BandLemmaThird
