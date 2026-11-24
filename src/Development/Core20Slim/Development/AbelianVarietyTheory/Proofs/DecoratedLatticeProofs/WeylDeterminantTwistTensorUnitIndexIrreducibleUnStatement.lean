module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorUnitIndexIrreducibleUn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary : ∀ (a : ℕ), 0 < a → ∀ (lam : Unit → DomWeight a) (n : Unit → ℕ), Vn lam n ≠ ⊥ ∧ ∀ U : Submodule ℂ (PY Unit a), U ≤ Vn lam n → (∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U) → U = ⊥ ∨ U = Vn lam n := by
  first | exact @GlobalTheory.KJInf.Vn_unit_irreducible | exact GlobalTheory.KJInf.Vn_unit_irreducible | (intros; apply GlobalTheory.KJInf.Vn_unit_irreducible <;> assumption)
