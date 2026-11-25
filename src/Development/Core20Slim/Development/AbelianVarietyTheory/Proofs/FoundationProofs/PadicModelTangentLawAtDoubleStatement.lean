module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelTangentLawAtDouble
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
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
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
theorem _root_.GlobalTheory.T.padicModel_tangentLaw_at_double : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  first | exact @GlobalTheory.ModelDouble.tangent_law | exact GlobalTheory.ModelDouble.tangent_law | (intros; apply GlobalTheory.ModelDouble.tangent_law <;> assumption)
