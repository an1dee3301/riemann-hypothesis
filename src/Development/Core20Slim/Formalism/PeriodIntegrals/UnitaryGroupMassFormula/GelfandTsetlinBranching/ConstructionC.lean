module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.NatWAntiC
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.PeriodIntegrals.HwIrred
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem realize_of (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) : Realize := by
  intro n N hN lam mu f hf hfix hne
  subst hN
  exact realize_C h he ha n lam mu f hf hfix hne

end PI.WGB
