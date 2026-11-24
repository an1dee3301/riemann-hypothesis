module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
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
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), ¬ JointShape p q r s μ μ' → hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s) = ⊥ := by
  first | exact @GlobalTheory.FockAlg.jointHarm_hw_eq_bot | exact GlobalTheory.FockAlg.jointHarm_hw_eq_bot | (intros; apply GlobalTheory.FockAlg.jointHarm_hw_eq_bot <;> assumption)
