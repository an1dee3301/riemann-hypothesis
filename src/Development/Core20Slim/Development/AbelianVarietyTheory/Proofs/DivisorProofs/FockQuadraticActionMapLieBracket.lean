module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivPderivCommFock
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockLie

theorem weyl_comm {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [DecidableEq ι] (a b : ι → A)
    (h : ∀ l m, (b l * a m - a m * b l = if l = m then (1 : A) else 0) ∧
      b l * b m = b m * b l ∧ a l * a m = a m * a l) (i j k l : ι) :
    (a i * b j) * (a k * b l) - (a k * b l) * (a i * b j) =
      (if j = k then a i * b l else 0) - (if l = i then a k * b j else 0) := by
  have h1 : b j * a k = a k * b j + if j = k then (1 : A) else 0 := by
    rw [← (h j k).1]; abel
  have h2 : b l * a i = a i * b l + if l = i then (1 : A) else 0 := by
    rw [← (h l i).1]; abel
  have e1 : (a i * b j) * (a k * b l) = a i * (b j * a k) * b l := by simp only [mul_assoc]
  have e2 : (a k * b l) * (a i * b j) = a k * (b l * a i) * b j := by simp only [mul_assoc]
  have e3 : a i * (a k * b j) * b l = a k * (a i * b l) * b j := by
    calc a i * (a k * b j) * b l = (a i * a k) * (b j * b l) := by simp only [mul_assoc]
      _ = (a k * a i) * (b l * b j) := by rw [(h i k).2.2, (h j l).2.1]
      _ = _ := by simp only [mul_assoc]
  rw [e1, e2, h1, h2, mul_add, mul_add, add_mul, add_mul, e3]
  split_ifs <;> simp

theorem omE_comm {p q r s : ℕ} (i j k l : Ln p q r s) :
    omE i j * omE k l - omE k l * omE i j =
      (if j = k then omE i l else 0) - (if l = i then omE k j else 0) := by
  have h := weyl_comm (raiB : Ln p q r s → _) lowB (GlobalTheory.fock_letters_ccr p q r s) i j k l
  have e : omE i j * omE k l - omE k l * omE i j =
      (raiB i * lowB j) * (raiB k * lowB l) - (raiB k * lowB l) * (raiB i * lowB j) := by
    simp only [omE]
    split_ifs <;>
      simp only [add_zero, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] <;>
      module
  rw [e, h]
  simp only [omE]
  by_cases h1 : j = k <;> by_cases h2 : l = i
  · subst h1; subst h2; simp
  · have h3 : ¬ i = l := fun h => h2 h.symm
    simp [h1, h2, h3]
  · have h3 : ¬ k = j := fun h => h1 h.symm
    simp [h1, h2, h3]
  · simp [h1, h2]

theorem omAct_single {p q r s : ℕ} (i j : Ln p q r s) (x : ℂ) :
    omAct p q r s (Matrix.single i j x) = x • omE i j := by
  rw [omAct_apply]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem omAct_single_mul {p q r s : ℕ} (i j k l : Ln p q r s) (x y : ℂ) :
    omAct p q r s (Matrix.single i j x * Matrix.single k l y) =
      (x * y) • (if j = k then omE i l else 0) := by
  by_cases h : j = k
  · subst h
    rw [Matrix.single_mul_single_same, omAct_single, if_pos rfl]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, if_neg h, map_zero, smul_zero]

theorem omAct_lie (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s (Y * Z - Z * Y) =
      omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  induction Y using Matrix.induction_on' with
  | h_zero => simp
  | h_add Y Y' hY hY' =>
    have : (Y + Y') * Z - Z * (Y + Y') = (Y * Z - Z * Y) + (Y' * Z - Z * Y') := by
      rw [add_mul, mul_add]; abel
    rw [this, map_add (f := _), hY, hY', map_add (f := _), add_mul, mul_add]; abel
  | h_std_basis i j x =>
    induction Z using Matrix.induction_on' with
    | h_zero => simp
    | h_add Z Z' hZ hZ' =>
      have : Matrix.single i j x * (Z + Z') - (Z + Z') * Matrix.single i j x =
          (Matrix.single i j x * Z - Z * Matrix.single i j x) +
            (Matrix.single i j x * Z' - Z' * Matrix.single i j x) := by
        rw [add_mul, mul_add]; abel
      rw [this, map_add (f := _), hZ, hZ', map_add (f := _), add_mul, mul_add]; abel
    | h_std_basis k l y =>
      rw [map_sub, omAct_single_mul, omAct_single_mul, omAct_single, omAct_single,
        smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub, ← smul_sub, omE_comm]

end GlobalTheory.FockLie
