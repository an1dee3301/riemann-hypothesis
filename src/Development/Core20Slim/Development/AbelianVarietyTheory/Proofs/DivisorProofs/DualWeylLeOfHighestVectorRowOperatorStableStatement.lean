module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.GelfA
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M → (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  first | exact @GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | exact GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | (intros; apply GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable <;> assumption)
