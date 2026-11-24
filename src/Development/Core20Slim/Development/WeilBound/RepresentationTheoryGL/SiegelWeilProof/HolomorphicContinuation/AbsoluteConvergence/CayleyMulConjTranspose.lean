module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open scoped Matrix
open Matrix

noncomputable section

namespace PositivityTheory.Rg.Sw.KAKB

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def S0 (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

def C0 (n : ℕ) : M2 n := fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))

def C1 (n : ℕ) : M2 n := (1 / 2 : ℂ) • (C0 n)ᴴ

theorem cayley_conjTranspose_eq : (C0 n)ᴴ = fromBlocks 1 (-(Complex.I • 1)) 1 (Complex.I • 1) := by
  simp [C0, fromBlocks_conjTranspose, conjTranspose_smul]

theorem cayley_conjTranspose_mul : (C0 n)ᴴ * C0 n = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_mul_conjTranspose : C0 n * (C0 n)ᴴ = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_inverse_mul : C1 n * C0 n = 1 := by
  rw [C1, Matrix.smul_mul, cayley_conjTranspose_mul, smul_smul]; norm_num

theorem cayley_mul_inverse : C0 n * C1 n = 1 := by
  rw [C1, Matrix.mul_smul, cayley_mul_conjTranspose, smul_smul]; norm_num

theorem complex_structure_cayley : JJ n * C0 n = C0 n * (Complex.I • S0 n) := by
  simp only [JJ, C0, S0, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;> module

end PositivityTheory.Rg.Sw.KAKB

end
