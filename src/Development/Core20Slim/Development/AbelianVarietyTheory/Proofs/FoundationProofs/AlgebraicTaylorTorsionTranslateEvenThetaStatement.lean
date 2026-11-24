module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
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
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.IntermediateField.Basic

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
