module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicPropertiesStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem IsLat.evenTheta_translate_sq_eq_sigmaStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  intro Λ h t₀ h0 h2 t ht z
  have hsq := (GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ h0 h2).2.2.2.1 (z + t)
  have hσ := (h.sg_eq_zero t).not.2 ht
  rw [h.sqTh_sub h0 ht] at hsq
  have hs : sqTh Λ t (z + t) * sgStar Λ t ^ 2 = -(sgStar Λ (z + 2 * t) * sgStar Λ z) := by
    rw [sqTh, div_mul_cancel₀ _ (pow_ne_zero 2 hσ), show t - (z + t) = -z by ring, h.sg_neg,
      show t + (z + t) = z + 2 * t by ring]
    ring
  simp only [U1, zero_add, mul_pow]
  rw [hsq]
  have he : Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) (2 * t) / ↑(area Λ) -
        ↑Real.pi * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * ↑(area Λ))) =
      Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 *
      Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 := by
    rw [← mul_pow, ← Complex.exp_add, sq, ← Complex.exp_add, map_mul, map_ofNat]
    congr 1
    ring
  rw [he]
  generalize Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = a
  generalize Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = b
  linear_combination a ^ 2 * b ^ 2 * hs

end GlobalTheory.EvenTheta
