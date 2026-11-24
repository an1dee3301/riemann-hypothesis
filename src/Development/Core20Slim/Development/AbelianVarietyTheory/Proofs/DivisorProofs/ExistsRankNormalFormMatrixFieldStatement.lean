module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankNormalFormMatrixField
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_normal_form_matrix_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  first | exact @GlobalTheory.rank_normal_form_field | exact GlobalTheory.rank_normal_form_field | (intros; apply GlobalTheory.rank_normal_form_field <;> assumption)
