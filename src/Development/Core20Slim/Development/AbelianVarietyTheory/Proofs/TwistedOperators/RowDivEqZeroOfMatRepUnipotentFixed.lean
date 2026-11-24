module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
public import Formalism.GradedWeylDivisibility.StatementA
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
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

private theorem rowGen_eval_C_eq_rowAct_transvection {n n' : ℕ} (a b : Fin n') (t : ℂ)
    (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (Matrix.transvection a b t)ᵀ f := by
  have key : (Polynomial.evalRingHom (C t : MvPolynomial (Fin n' × Fin n) ℂ)).comp
      (rowGen ℂ (n := n) a b).toRingHom = (rowAct ℂ (n := n) (Matrix.transvection a b t)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · rintro ⟨i, s⟩
      by_cases h : i = b
      · subst h
        simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, ite_and, add_comm]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp), if_pos rfl, mul_comm]
      · simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, h, Ne.symm h]
  exact RingHom.congr_fun key f

theorem rowDiv_eq_zero_of_matRep_unipotent_fixed : ∀ (n n' : ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n') ℂ, (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n') (Fin n') ℂ) a a = 1) → matRep n n' (1, g) v = v) → ∀ a b : Fin n', a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
  intro n n' v hv a b hab k hk
  have hroot : ∀ t : ℂ, (rowGen ℂ a b v).eval (C t) = v := by
    intro t
    rw [rowGen_eval_C_eq_rowAct_transvection]
    have hdet : IsUnit (Matrix.transvection a b t).det := by
      rw [Matrix.det_transvection_of_ne _ _ (ne_of_lt hab)]
      exact isUnit_one
    let g : GL (Fin n') ℂ := Matrix.nonsingInvUnit _ hdet
    have hgv : (g : Matrix (Fin n') (Fin n') ℂ) = Matrix.transvection a b t := rfl
    have hbt : (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := fun h => by simp [h] at hij
      have hne' : ¬(a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact absurd (lt_trans hab hij) (lt_irrefl _)
      simp [hgv, Matrix.transvection, Matrix.single, hne, hne']
    have hdiag : ∀ i, (g : Matrix (Fin n') (Fin n') ℂ) i i = 1 := by
      intro i
      have hne' : ¬(a = i ∧ b = i) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [hgv, Matrix.transvection, Matrix.single, hne']
    have hg := hv g hbt hdiag
    rw [matRep_one_left, hgv] at hg
    exact hg
  have hconst : rowGen ℂ a b v = Polynomial.C v := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_
      (Set.infinite_range_of_injective (MvPolynomial.C_injective (Fin n' × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    simp [Polynomial.IsRoot, hroot t]
  show (rowGen ℂ a b v).coeff k = 0
  rw [hconst, Polynomial.coeff_C, if_neg (by omega)]

end GlobalTheory.GLDuality
