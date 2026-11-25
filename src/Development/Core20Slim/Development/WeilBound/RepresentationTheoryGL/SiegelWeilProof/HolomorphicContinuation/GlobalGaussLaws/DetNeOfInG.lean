module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

theorem det_JJ_ne : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg] at this
  simp at this

theorem det_ne_of_inG {g : M2 n} (h : InG g) : g.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact det_JJ_ne this.symm

def mkG (g : M2 n) (h : InG g) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g (det_ne_of_inG h), h⟩

@[simp] theorem mR_mkG (g : M2 n) (h : InG g) : mR (mkG g h) = g := rfl

theorem inG_nU (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : InG (nU b) := by
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]

theorem inG_nbar (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) : InG (nbar c) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]

theorem inG_mM (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : InG (mM a) := by
  have hu : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  simp [InG, mM, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ ha]

def kth (θ : Fin n → ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ)) (diagonal fun j => (Real.sin (θ j) : ℂ))
    (-diagonal fun j => (Real.sin (θ j) : ℂ)) (diagonal fun j => (Real.cos (θ j) : ℂ))

theorem inK_kth (θ : Fin n → ℝ) : InK (kth θ) := by
  have hcs : ∀ j : Fin n, (Real.cos (θ j) : ℂ) * Real.cos (θ j) + (Real.sin (θ j) : ℂ) * Real.sin (θ j) = 1 := by
    intro j
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  have hsc : ∀ j : Fin n, (Real.sin (θ j) : ℂ) * Real.sin (θ j) + (Real.cos (θ j) : ℂ) * Real.cos (θ j) = 1 := by
    intro j
    rw [add_comm]
    exact hcs j
  refine ⟨?_, ?_⟩
  · simp [InG, kth, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    refine ⟨?_, ?_, ?_⟩
    · funext i
      rw [Pi.zero_apply]
      ring
    · ext i j
      rw [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs
      · linear_combination -(hcs i)
      · simp
    · funext i
      rw [Pi.zero_apply]
      ring
  · simp [kth, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    have h0 : (Matrix.diagonal fun i : Fin n => (Real.cos (θ i) : ℂ) * Real.sin (θ i) +
        -((Real.sin (θ i) : ℂ) * Real.cos (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    have h1 : (Matrix.diagonal fun i : Fin n => (Real.sin (θ i) : ℂ) * Real.cos (θ i) +
        -((Real.cos (θ i) : ℂ) * Real.sin (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    rw [h0, h1, Matrix.fromBlocks_one]

end PositivityTheory.Rg.Sw.Glob.VacB
