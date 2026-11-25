module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Prod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      monomial d ((d.prod fun x e => (t x.2 : ℂ) ^ e) * c) := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ =
      aeval (fun x : Fin n' × Fin n => C (t x.2 : ℂ) * (X x : MvPolynomial (Fin n' × Fin n) ℂ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, diagGL, Fintype.sum_prod_type, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  rw [matRep_apply, h, aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, algebraMap_eq]
  ring

theorem coeff_matRep_diagGL_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (v : MvPolynomial (Fin n' × Fin n) ℂ)
    (d : Fin n' × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (matRep n n' (diagGL ℂ n t, 1) v) d = (d.prod fun x e => (t x.2 : ℂ) ^ e) * AddMonoidAlgebra.coeff v d := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [matRep_diagGL_monomial_colChar, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem colAdd_eq_matRep_of_transvection {n n' : ℕ} (l j : Fin n) (c : ℂ) (g : GL (Fin n) ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) : colAdd ℂ l j c v = matRep n n' (g, 1) v := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      (g : Matrix (Fin n) (Fin n) ℂ))ᵀ = colAdd ℂ (r := n') l j c := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [hg]
    by_cases hs : s = j
    · subst hs
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, add_mul, Finset.sum_add_distrib]
    · have hs' : ¬ j = s := fun e => hs e.symm
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, hs, hs']
  rw [matRep_apply, h]

theorem mem_dualWeyl_of_unitriangular_fixed :
    ∀ (n n' : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → matRep n n' (g, 1) v = v) → (∀ t : Fin n → ℂˣ, matRep n n' (diagGL ℂ n t, 1) v = (∏ a, (t a : ℂ) ^ ν a) • v) → v ∈ dualWeyl ℂ n' n ν := by
  intro n n' ν v hU hT
  rw [Formalism.GradedWeylDivisibility.dualWeylPoint ℂ n' n ν v]
  refine ⟨fun d hd => ?_, fun l j hlj c => ?_⟩
  · funext i
    let t : Fin n → ℂˣ := fun s => if s = i then Units.mk0 2 two_ne_zero else 1
    have h1 := congrArg (AddMonoidAlgebra.coeff · d) (hT t)
    rw [coeff_matRep_diagGL_colChar, coeff_smul, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hd h1
    have h3 : (∏ a, (t a : ℂ) ^ ν a) = 2 ^ ν i := by
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro b _ hb
        simp [t, hb]
      · simp
    have h4 : (d.prod fun x e => (t x.2 : ℂ) ^ e) = 2 ^ (Finsupp.weight (colW n' n) d i) := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      by_cases hx : x.2 = i
      · simp [t, colW, hx]
      · simp [t, colW, hx]
    rw [h3, h4] at h2
    have h5 : (2 : ℕ) ^ (Finsupp.weight (colW n' n) d i) = 2 ^ ν i := by exact_mod_cast h2
    exact Nat.pow_right_injective le_rfl h5
  · have hne : l ≠ j := hlj.ne
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection l j c)
      (by rw [Matrix.det_transvection_of_ne l j hne]; exact one_ne_zero)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c := rfl
    rw [colAdd_eq_matRep_of_transvection l j c g hg]
    refine hU g ?_ ?_
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ (l = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlj hab'
      rw [hg]
      simp [Matrix.transvection, h1, Matrix.one_apply_ne hab'.ne']
    · intro a
      have h1 : ¬ (l = a ∧ j = a) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      rw [hg]
      simp [Matrix.transvection, h1]

end GlobalTheory.GLDuality
