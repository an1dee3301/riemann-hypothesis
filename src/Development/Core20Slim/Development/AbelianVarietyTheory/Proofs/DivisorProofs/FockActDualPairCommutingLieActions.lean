module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracketStatement
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH
open scoped Kronecker

namespace GlobalTheory.FockPair

theorem fockAct1_eq_kron (p q r s : ℕ) (Y : Mat p q) :
    fockAct1 p q r s Y = omAct p q r s (Y ⊗ₖ (1 : Mat r s)) := rfl

theorem fockAct2_eq_kron (p q r s : ℕ) (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s ((1 : Mat p q) ⊗ₖ Z) := rfl

theorem pair_lie_commute : ∀ (p q r s : ℕ), IsLieAct (fockAct1 p q r s) ∧
    IsLieAct (fockAct2 p q r s) ∧ ∀ (Y : Mat p q) (Z : Mat r s),
      fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  intro p q r s
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩
  · rw [map_sub]
    simp only [fockAct1_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [map_sub]
    simp only [fockAct2_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← GlobalTheory.T.fockQuadraticAction_map_lie_bracket,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end GlobalTheory.FockPair
