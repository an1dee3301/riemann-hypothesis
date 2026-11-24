module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory

theorem coverUnitary_unimodular :
    ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧
      LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G :=
  fun p q T => ⟨(GlobalTheory.HolDS.haar_unimodular p q T).1, (GlobalTheory.HolDS.haar_unimodular p q T).2,
    GlobalTheory.HolDS.instLocallyCompact T, GlobalTheory.HolDS.instSecondCountable T, GlobalTheory.HolDS.t2Space_cuspAdeles T⟩

end GlobalTheory
