module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.OrderDual
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorTri

theorem sum_fin_eq_sum_castLE_of_vanish {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ)
    (hf : ∀ k : Fin n, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin l, f (Fin.castLE hl k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) ((Fin.castLE_injective hl).injOn) (by simp) ?_ (by simp)
  intro k _ hk
  apply hf
  by_contra h
  exact hk ⟨⟨k.val, by omega⟩, by simp, rfl⟩

theorem leadBlock_lower_mul {n l : ℕ} (hl : l ≤ n) (c z : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, i < j → c i j = 0) :
    (c * z).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      c.submatrix (Fin.castLE hl) (Fin.castLE hl) * z.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => c (Fin.castLE hl i) k * z k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc _ k (by rw [Fin.lt_def]; have := i.isLt; simp only [Fin.val_castLE]; omega), zero_mul]

theorem leadBlock_mul_upper {n l : ℕ} (hl : l ≤ n) (z c : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, j < i → c i j = 0) :
    (z * c).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      z.submatrix (Fin.castLE hl) (Fin.castLE hl) * c.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => z (Fin.castLE hl i) k * c k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc k _ (by rw [Fin.lt_def]; have := j.isLt; simp only [Fin.val_castLE]; omega), mul_zero]

theorem leadMinor_lower_mul_mul_upper :
    ∀ (n : ℕ) (c z c' : Matrix (Fin n) (Fin n) ℂ), (∀ i j, i < j → c i j = 0) → (∀ i j, j < i → c' i j = 0) → ∀ (l : ℕ) (hl : l ≤ n), leadMinor (c * z * c') l hl = (∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) * c' (Fin.castLE hl i) (Fin.castLE hl i)) * leadMinor z l hl := by
  intro n c z c' hc hc' l hl
  have h1 : (c.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_lowerTriangular
    intro i j hij
    exact hc _ _ (show i < j from hij)
  have h2 : (c'.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c' (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_upperTriangular
    intro i j hij
    exact hc' _ _ (show j < i from hij)
  change ((c * z * c').submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
    _ * (z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
  rw [leadBlock_mul_upper hl _ _ hc', leadBlock_lower_mul hl _ _ hc, Matrix.det_mul, Matrix.det_mul,
    h1, h2, Finset.prod_mul_distrib]
  ring

end GlobalTheory.LeadMinorTri
