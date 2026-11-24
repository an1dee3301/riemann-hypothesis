module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelChordLawSumAndDifference
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicModel_chordLaw_sum_and_difference : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  first | exact @GlobalTheory.ThetaPar.Chord.model_chord | exact GlobalTheory.ThetaPar.Chord.model_chord | (intros; apply GlobalTheory.ThetaPar.Chord.model_chord <;> assumption)
