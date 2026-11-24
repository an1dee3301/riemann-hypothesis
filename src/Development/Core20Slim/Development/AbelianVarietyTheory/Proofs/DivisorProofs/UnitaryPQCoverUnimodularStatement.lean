module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodular
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPQCover_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧ LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G := by
  first | exact @GlobalTheory.coverUnitary_unimodular | exact GlobalTheory.coverUnitary_unimodular | (intros; apply GlobalTheory.coverUnitary_unimodular <;> assumption)
