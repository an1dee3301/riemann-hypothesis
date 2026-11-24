module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.RealGroupsLie
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace GroundTheory.Automorphic

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

section TraceForm

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))

variable {L}

end TraceForm

section Positivity

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Positivity

section Cartan

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))

variable {L}


end Cartan

section MaxCompact

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

def maxCompact (G : Subgroup (Matrix ι ι 𝕜)ˣ) : Subgroup G where
  carrier := {g | ((g : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜}
  mul_mem' {a b} ha hb := by
    change ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) * ((b : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈
      Matrix.unitaryGroup ι 𝕜
    exact Submonoid.mul_mem _ ha hb
  one_mem' := by
    change ((1 : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜
    rw [Units.val_one]
    exact Submonoid.one_mem _
  inv_mem' {a} ha := by
    change (((a : (Matrix ι ι 𝕜)ˣ)⁻¹ : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜
    have hmul : ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) *
        star ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) = 1 := Matrix.mem_unitaryGroup_iff.1 ha
    rw [Units.inv_eq_of_mul_eq_one_right hmul]
    exact Unitary.star_mem ha



end MaxCompact

section Groups

open NormedSpace
open scoped Matrix.Norms.L2Operator


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Groups

end GroundTheory.Automorphic
