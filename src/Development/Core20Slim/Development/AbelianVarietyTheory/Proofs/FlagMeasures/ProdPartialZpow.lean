module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFinEqSumCastLEOfVanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
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
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic

@[expose] public section

open Matrix Finset Formalism.MainNotions.S GlobalTheory.Dec

namespace GlobalTheory.PhiTriangular

theorem sum_sInt_from {n : ℕ} (lam : Fin n → ℝ) (l : Fin n) :
    ∑ i : Fin n, (if l ≤ i then sInt lam i else 0) = muInt lam l := by
  let m : ℕ → ℤ := fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) =
      m (max i.val l.val) - m (max (i.val + 1) l.val) := by
    intro i
    by_cases h : l ≤ i
    · have h' : l.val ≤ i.val := h
      rw [if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]
      simp only [m, sInt, dif_pos i.isLt]
    · have h' : i.val < l.val := by simpa using h
      rw [if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n,
    Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _),
    max_eq_left l.isLt.le]
  simp [m]

theorem prod_castLE_succ {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j) = ∏ l : Fin n, if l ≤ i then d l else 1 := by
  refine Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩
  · intro j _
    rw [if_pos]
    exact Nat.le_of_lt_succ j.isLt

theorem zpow_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ) {a : ℂ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem prod_partial_zpow {n : ℕ} (lam : Fin n → ℝ) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) :
    ∏ i : Fin n, (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) ^ (-(sInt lam i)) =
      ∏ l, d l ^ (-(muInt lam l)) := by
  simp only [prod_castLE_succ, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : l ≤ i <;> simp [h]

theorem phiTri : PhiTri := by
  intro n lam c z c' hc hc' hd hz
  have hd' : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hd l).1 (hd l).2
  refine ⟨fun i => ?_, ?_⟩
  · rw [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)
  · unfold Phi
    simp only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]
    rw [Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']

end GlobalTheory.PhiTriangular
