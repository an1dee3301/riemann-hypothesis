module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
