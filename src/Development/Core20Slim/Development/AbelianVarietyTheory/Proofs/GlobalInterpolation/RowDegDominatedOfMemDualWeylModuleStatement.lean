module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModule
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support, (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧ ∑ a, rowDeg m a = ∑ a, ν a := by
  first | exact @GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | exact GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | (intros; apply GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl <;> assumption)
