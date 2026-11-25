module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateProductSigmaStarPowLatticeLaw
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslateProduct_sigmaStarPow_lattice_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  first | exact @GlobalTheory.ThetaLaw.pull_law | exact GlobalTheory.ThetaLaw.pull_law | (intros; apply GlobalTheory.ThetaLaw.pull_law <;> assumption)
