module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

def colA (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := sgStar Λ z ^ 3

def colB (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)

def colC (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z

def tay (F : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 F)

def defect {R : Type*} [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) :
    MvPowerSeries (Fin 3) R :=
  Matrix.det (Matrix.of fun i j =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) : MvPowerSeries (Fin 3) R)) -
    2 * PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 1 - MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 2 - MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) s

end GlobalTheory.FrobStick
