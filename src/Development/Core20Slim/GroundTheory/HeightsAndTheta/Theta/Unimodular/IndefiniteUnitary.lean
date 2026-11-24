module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Theta.Cartan
public import Development.Core20Slim.GroundTheory.AutomorphicForms.RealGroupsLie
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace GroundTheory.Heights₂.Theta

open MeasureTheory Matrix GroundTheory.Automorphic
open scoped NNReal ComplexOrder MatrixOrder

noncomputable section

variable {p q : ℕ}

def indefJElem (p q : ℕ) : indefiniteUnitaryGroup p q :=
  upqOfMatrix (indefJ p q) (by rw [indefJ_conjTranspose, indefJ_mul_self, Matrix.one_mul])

theorem indefJElem_mul_self : indefJElem p q * indefJElem p q = 1 :=
  Subtype.ext (Units.ext (indefJ_mul_self p q))

theorem indefJElem_mul_mul_indefJElem (s : cartanPos p q) :
    indefJElem p q * upqOfMatrix s.1 s.2.2 * indefJElem p q = (upqOfMatrix s.1 s.2.2)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change indefJ p q * s.1 * indefJ p q = indefJ p q * s.1ᴴ * indefJ p q
  rw [s.2.1.isHermitian.eq]

variable [MeasurableSpace (indefiniteUnitaryGroup p q)] [BorelSpace (indefiniteUnitaryGroup p q)]

end

end GroundTheory.Heights₂.Theta
