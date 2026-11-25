module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPSeriesAndSigmaStarQuotientSeri
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  first | exact @GlobalTheory.WpSeries.exists_wpSer | exact GlobalTheory.WpSeries.exists_wpSer | (intros; apply GlobalTheory.WpSeries.exists_wpSer <;> assumption)
