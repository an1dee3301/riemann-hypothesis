module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Dbl.ColBlocks

theorem mul_transpose_doubledSpaceFrame_toCols1 {α β : Type} [Fintype β] {R S : ℕ} (M : Matrix α (Ix (R + S) (S + R)) ℂ) (C : Matrix β (Ix R S) ℂ) :
    (M * (dblM C)ᵀ).toCols₁ =
      M.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ := by
  ext a i
  simp only [Matrix.toCols₁, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    dblM, Fintype.sum_sum_type, Fin.sum_univ_add, dblCol, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]

theorem mul_transpose_doubledSpaceFrame_toCols2 {α β : Type} [Fintype β] {R S : ℕ} (M : Matrix α (Ix (R + S) (S + R)) ℂ) (C : Matrix β (Ix R S) ℂ) :
    (M * (dblM C)ᵀ).toCols₂ =
      M.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ := by
  ext a i
  simp only [Matrix.toCols₂, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    dblM, Fintype.sum_sum_type, Fin.sum_univ_add, dblCol, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]
  ring

theorem mul_submatrix_right {α γ δ ε : Type} [Fintype γ] (A : Matrix α γ ℂ) (c : Matrix γ δ ℂ) (e : ε → δ) :
    A * c.submatrix id e = (A * c).submatrix id e := rfl

theorem jm_right_L {γ : Type} {R S : ℕ} (X : Matrix γ (Ix (R + S) (S + R)) ℂ) :
    (X * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      X.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Jm R S := by
  ext a k
  rcases k with r | s <;>
  simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem jm_right_R {γ : Type} {R S : ℕ} (X : Matrix γ (Ix (R + S) (S + R)) ℂ) :
    (X * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(X.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Jm R S) := by
  ext a k
  rcases k with r | s <;>
  simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

end GlobalTheory.RealLift.Dbl.ColBlocks

namespace GlobalTheory.RealLift.Dbl


open GlobalTheory.RealLift.Dbl.ColBlocks in
theorem dblM_colBlocks : ∀ (α β : Type) [Fintype β] (P Q R S : ℕ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ),
    (A * c * (dblM C)ᵀ).toCols₁ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) *
        Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) *
        Jm R S) := by
  intro α β _ P Q R S A C c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_transpose_doubledSpaceFrame_toCols1, mul_submatrix_right]
  · rw [mul_transpose_doubledSpaceFrame_toCols2, mul_submatrix_right]
  · rw [jm_right_L, mul_submatrix_right]
  · rw [jm_right_R, mul_submatrix_right]

end GlobalTheory.RealLift.Dbl
