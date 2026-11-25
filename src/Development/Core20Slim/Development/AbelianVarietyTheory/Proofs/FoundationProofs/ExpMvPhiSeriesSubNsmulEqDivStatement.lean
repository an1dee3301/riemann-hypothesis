module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDiv
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul | exact GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul | (intros; apply GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul <;> assumption)
