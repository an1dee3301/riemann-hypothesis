module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open GlobalTheory.WeilM
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCell_factorisation_doubledUnitaryGroup : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (c : R →ₐ[A] R) [Invertible (2 : R)] (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β R) (g : UG c (dbl J)), IsUnit (Matrix.fromCols (1 : Matrix β β R) (-1 : Matrix β β R) * ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R)).det → ∃ (p q : UG c (dbl J)) (t s : GL β R), ((p : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) = Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) * (t : Matrix β β R) ∧ ((q : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) = Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) * (s : Matrix β β R) ∧ g = p * q := by
  first | exact @GlobalTheory.BigCell.bigCell_factor | exact GlobalTheory.BigCell.bigCell_factor | (intros; apply GlobalTheory.BigCell.bigCell_factor <;> assumption)
