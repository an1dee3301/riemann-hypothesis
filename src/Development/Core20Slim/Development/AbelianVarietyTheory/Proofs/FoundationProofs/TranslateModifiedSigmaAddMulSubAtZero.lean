module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem translate_modifiedSigma_add_mul_sub_at_zero :
    ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ →
      U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 =
        (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  intro Λ hΛ P Q hP hQ
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).2.2.2.1 P Q hP hQ
  have hσ : sgStar Λ (P + Q) * sgStar Λ (P - Q) =
      (wpF Λ Q - wpF Λ P) * sgStar Λ P ^ 2 * sgStar Λ Q ^ 2 := by
    linear_combination hlaw
  simp only [U1, zero_add, mul_zero, zero_mul, zero_div, zero_sub]
  have hexp : ∀ x : ℂ, Complex.exp x ^ 2 = Complex.exp (2 * x) := by
    intro x; rw [← Complex.exp_nat_mul]; norm_num
  have key : Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ)))) =
      Complex.exp (-(↑Real.pi * P * (starRingEnd ℂ) P / (2 * ↑(area Λ)))) ^ 2 *
      Complex.exp (-(↑Real.pi * Q * (starRingEnd ℂ) Q / (2 * ↑(area Λ)))) ^ 2 := by
    rw [hexp, hexp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add (f := _), map_sub]
    ring
  calc _ = (sgStar Λ (P + Q) * sgStar Λ (P - Q)) *
      (Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ))))) := by ring
    _ = _ := by rw [hσ, key]; ring

end GlobalTheory
