module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.PeriodIntegrals.HwIrred
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.OrderDual
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem natW_add_A {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) + lam.detShift = lam.w i := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i :=
    lam.anti (show i ≤ ⟨N - 1, by omega⟩ by rw [Fin.le_def]; simp; omega)
  unfold DomWeight.natW DomWeight.detShift
  rw [dite_eq_left hN, Int.toNat_of_nonneg (by omega)]
  ring

theorem natW_anti_A {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem sqAct_mem_nabla_A (n : ℕ) (mu : DomWeight n) (g : GL (Fin n) ℂ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    sqAct ℂ n mu g s ∈ nablaSq ℂ n mu := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n mu.natW _ s hs)

theorem rowAct_X_A {r n : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r × Fin n) :
    Formalism.GradedWeylDivisibility.rowAct ℂ M (X v) = ∑ b : Fin r, C (M v.1 b) * X (b, v.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem rowAct_lpMinor_A (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (s : ℕ) (hs : s ≤ n) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M (Formalism.GradedWeylDivisibility.lpMinor ℂ s hs hs) = Formalism.GradedWeylDivisibility.lpMinor ℂ s hs hs := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have hmat : (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ)).map
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M) =
      (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) ℂ)) *
      Matrix.of fun p q : Fin s => (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ) := by
    ext p q
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [rowAct_X_A]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hs))), Finset.sum_map]
    · rfl
    · intro b _ hb
      have hbs : s ≤ b.val := by
        by_contra hlt
        apply hb
        exact Finset.mem_map.mpr ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
      simp only
      rw [hM _ _ (by rw [Fin.lt_def]; simp; omega), map_zero, zero_mul]
  have hL : (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) ℂ)).IsLowerTriangular := by
    intro i j hij
    simp only [Matrix.of_apply]
    rw [hM _ _ (by rw [Fin.lt_def]; simpa using hij), map_zero]
  rw [hmat, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL]
  simp [hd]

theorem rowAct_hw_A (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) = Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν := by
  unfold Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rowAct_lpMinor_A n M hM hd]

theorem det_unitri_A (n : ℕ) (g : GL (Fin n) ℂ) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular]
  · simp [hd]
  · intro i j hij
    exact hl i j hij

theorem extremalFacts_proof_A : ExtremalFacts := by
  intro n mu
  refine ⟨?_, ?_, fun g s hs => sqAct_mem_nabla_A n mu g s hs⟩
  · intro g hl hd
    unfold sqAct detPow extremal
    rw [det_unitri_A n g hl hd, one_zpow, Units.val_one, one_smul]
    apply rowAct_hw_A
    · intro i j hij
      simp only [Matrix.transpose_apply]
      exact hl j i hij
    · intro i
      simp only [Matrix.transpose_apply]
      exact hd i
  · intro t
    unfold sqAct detPow extremal
    have hdiag : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose =
        Matrix.diagonal fun a => (t a : ℂ) := by
      simp [diagGL]
    rw [hdiag, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ n n _ _ _
      (Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl mu.natW (natW_anti_A mu)), smul_smul]
    congr 1
    have hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ n t) = ∏ a, t a := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL, Matrix.det_diagonal]
    have hrow : ∀ a : Fin n, Formalism.GradedWeylDivisibility.rowNu (r := n) mu.natW a = mu.natW a := by
      intro a
      simp [Formalism.GradedWeylDivisibility.rowNu]
    simp only [hrow, hdet]
    have key : (∏ a, t a) ^ mu.detShift * ∏ a, t a ^ ((mu.natW a : ℕ) : ℤ) = ∏ a, t a ^ mu.w a := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← zpow_add, add_comm, natW_add_A]
    rw [← key, Units.val_mul, Units.coe_prod]
    simp [zpow_natCast]

theorem extremalFacts_of_A (_h : PI.HwIrred) : ExtremalFacts := extremalFacts_proof_A

end PI.WGB
