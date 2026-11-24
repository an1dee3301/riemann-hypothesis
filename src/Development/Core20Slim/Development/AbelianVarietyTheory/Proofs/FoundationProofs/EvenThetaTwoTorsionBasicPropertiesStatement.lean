module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (GL3Theta.th0 Λ t₀) ∧ GL3Theta.th0 Λ t₀ 0 = 1 ∧ (∀ z, GL3Theta.th0 Λ t₀ (-z) = GL3Theta.th0 Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z ^ 2 = sqTh Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧ ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, U1 Λ ω (GL3Theta.th0 Λ t₀) z = GL3Theta.th0 Λ t₀ z := by
  first | exact @GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | exact GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | (intros; apply GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties <;> assumption)
