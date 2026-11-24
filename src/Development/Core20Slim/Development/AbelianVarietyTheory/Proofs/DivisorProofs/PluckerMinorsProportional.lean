module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open Matrix

namespace GlobalTheory

theorem det_mul_det_toBlocks₂₂_of_mul_eq_one {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X Y : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * Y = 1) :
    X.det * Y.toBlocks₂₂.det = X.toBlocks₁₁.det := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, X = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  obtain ⟨A', B', C', D', rfl⟩ : ∃ A B C D, Y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Y).symm⟩
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  have key : fromBlocks A B C D * fromBlocks (1 : Matrix m m K) B' 0 D' = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply, h12, h22]
    simp
  have := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at this
  simpa using this

end GlobalTheory
