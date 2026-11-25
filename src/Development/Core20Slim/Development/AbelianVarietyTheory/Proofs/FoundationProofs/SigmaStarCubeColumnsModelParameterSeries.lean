module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_atU {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) (hσ : AlgEnt (sgStar g.abelian₂)) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  have h0 : coef1 (sgStar g.abelian₂) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar g.abelian₂)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar g.abelian₂) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  have hS' : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * PowerSeries.map g.lam S := by
    rw [GlobalTheory.EvenTheta.Param.theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X]
  have hE := GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g _ hS'
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, hS', subst_mul hs, subst_X hs, mul_assoc, mul_assoc, hE]

theorem colAB_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hT, hC, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨aT, eT⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have e1 := sgStar_atU g hL hσ
  obtain ⟨⟨a2, e2⟩, -⟩ := hT _ _ hσ hσ
  obtain ⟨⟨a3, e3⟩, -⟩ := hT _ _ a2 hσ
  obtain ⟨aw, ew⟩ := hC _ hw
  obtain ⟨⟨a4, e4⟩, -⟩ := hT _ _ aw a2
  obtain ⟨-, a5, e5⟩ := hT _ _ aT a4
  obtain ⟨⟨a6, e6⟩, -⟩ := hT _ _ hσ a5
  have hA : colA g.abelian₂ = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z * sgStar g.abelian₂ z := by
    funext z; rw [colA]; ring
  have hB : colB g.abelian₂ v = fun z => sgStar g.abelian₂ z *
      (sqTh g.abelian₂ v z + wpF g.abelian₂ v * (sgStar g.abelian₂ z * sgStar g.abelian₂ z)) := by
    funext z; rw [colB]; ring
  rw [hA, hB]
  refine ⟨a3, a6, e1, ?_, ?_⟩
  · rw [e3, e2, e1, map_pow]; ring
  · rw [e6, e5, e4, e2, ew, eT, e1, lineSer, xAt]
    simp only [map_mul, map_pow, map_sub]
    ring

end GlobalTheory.FrobStick
