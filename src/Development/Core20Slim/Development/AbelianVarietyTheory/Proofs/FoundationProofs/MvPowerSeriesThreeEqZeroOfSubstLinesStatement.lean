module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_fin_three_eq_zero_of_subst_lines : ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines | exact GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines | (intros; apply GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines <;> assumption)
