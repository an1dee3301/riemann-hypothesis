module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.StatementA
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
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_genericDet (R : Type) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (lpMinor R n le_rfl le_rfl) = C g.det * lpMinor R n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 p q
  simp [rowAct, Matrix.mul_apply]

theorem genericDet_pow_mem (R : Type) [CommRing R] (n c : ℕ) :
    lpMinor R n le_rfl le_rfl ^ c ∈ dualWeyl R n n (fun _ => c) := by
  have h := bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)
  have e : shapeDeg (n := n) (fun _ : Fin c => n) = fun _ => c := by
    funext t
    simp [shapeDeg]
  rw [e] at h
  simpa [bideterminant, initMinor, lpMinor] using h

theorem genericDet_pow_mul_hw (R : Type) [CommRing R] (n c : ℕ) (ν : Fin n → ℕ) :
    lpMinor R n le_rfl le_rfl ^ c * hw R le_rfl ν = hw R (le_refl n) (fun i => ν i + c) := by
  cases n with
  | zero => simp [hw, lpMinor]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have hs : (Fin.castSucc s).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_pos hs]
      omega
    · have hs : ¬ (Fin.last m).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_neg hs, Nat.sub_zero]
      rw [pow_add, mul_comm]
      rfl

theorem genericDet_pow_mul :
    ∀ (n c : ℕ) (ν : Fin n → ℕ), (∀ f ∈ dualWeyl ℂ n n ν, lpMinor ℂ n le_rfl le_rfl ^ c * f ∈ dualWeyl ℂ n n (fun i => ν i + c)) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ), rowAct ℂ g (lpMinor ℂ n le_rfl le_rfl ^ c * f) = g.det ^ c • (lpMinor ℂ n le_rfl le_rfl ^ c * rowAct ℂ g f)) ∧ (Antitone ν → lpMinor ℂ n le_rfl le_rfl ^ c * hw ℂ le_rfl ν = hw ℂ (le_refl n) (fun i => ν i + c)) := by
  intro n c ν
  refine ⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩
  · rw [mul_comm]
    exact (dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)
  · rw [map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]

end GlobalTheory.Branching
