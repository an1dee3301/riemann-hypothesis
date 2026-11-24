module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Matrix

namespace GlobalTheory.UnitaryLieAlgebra

variable {n : Type*} [Fintype n]

def unitaryLie (J : Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
      smul_zero]

end GlobalTheory.UnitaryLieAlgebra
