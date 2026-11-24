module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePoStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIteratedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodingerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvariStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariableStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainThetaStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaParseval

theorem exists_lintegral_sq_eq_mul_setLIntegral_theta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  intro F _ _ ψ hψ κ _ μ hμ ν hν 𝓕 h𝓕
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F κ μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F κ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  refine ⟨(c₁ * μ 𝓕₁)⁻¹, fun Φ hΦ => ?_⟩
  have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F ψ hψ κ Φ hΦ
  have hG : @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) =>
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
  rw [hc _ hG (fun γ hγ w => by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F ψ hψ κ Φ γ hγ w])]
  simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F ψ hψ κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
  rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F κ μ hμ 𝓕₁ h𝓕₁ Φ hΦ, ← mul_assoc c₁, ← mul_assoc,
    ENNReal.inv_mul_cancel (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hctop htop), one_mul]

end GlobalTheory.ThetaParseval
