module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubeRelationOfParallelogram
public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglGram
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglPhSplit
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Development
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.AddPreservesExpCongruence
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.JetsPhW
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric 

theorem ph0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.ph = 0 := by
  unfold G1.ph
  rw [map_neg, neg_eq_zero]
  show logMv _ 0 = 0
  unfold logMv
  simp

theorem fglData {p : ℕ} [Fact p.Prime] (g : G1 p) (h : g.Ok) : PI.FglGram.Data g.l g.ex g.ph :=
  ⟨h.2.2.1, h.2.2.2, ph0 g⟩

theorem cube_of_two_identities_holds : CubeOfTwoIdentities := by
  intro p _ g h
  exact cube_relation_of_parallelogram p g.l g.ex g.ph (fglData g h)



theorem jetsHigh_holds : JetsHigh :=
  fun p _ g hOk => jets_high p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsOne_holds : JetsOne :=
  fun p _ g hOk => jets_one p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsTwo_holds : JetsTwo :=
  fun p _ g a b hOk => jets_two p g.W g.wq g.ex g.ph a b hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1
    hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
