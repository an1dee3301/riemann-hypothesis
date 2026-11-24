module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

theorem jointHarm_hw_eq_bot : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    ¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s) = ⊥ :=
  fun _ _ _ _ μ μ' => (GlobalTheory.JointHarm.joint_harmonics μ μ').2

end GlobalTheory.FockAlg
