module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size

namespace GlobalTheory.Chain.LiftConv

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f = thetaKO ω g h f := by
  intro γ hγ h

  have hsplit : ((g, γ * h) : GA D V × GA D W) = (1, γ) * (g, h) := by
    ext <;> simp
  have hpres : IsThetaFunO ψ V W (ω (g, h) f) := hω.om_pres _ _ hf
  unfold thetaKO
  rw [hsplit, map_mul, Module.End.mul_apply]
  exact hω.om_aut 1 (one_mem _) γ hγ _ hpres

theorem thetaKO_continuous (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    Continuous fun h => thetaKO ω g h f := by

  have hpair : Continuous fun h : GA D W => ((g, h) : GA D V × GA D W) := by fun_prop
  unfold thetaKO
  exact (hω.om_cont f hf 0).comp hpair

theorem thetaKO_modGrowth (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (g : GA D V) : ModGrowth W fun h => thetaKO ω g h f := by
  obtain ⟨A, d, hAd⟩ := hG V.rank W.rank
  obtain ⟨U, hUo, hfU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hf
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (hAd V W rfl rfl).real ψ hθ hUo
  obtain ⟨-, hbd⟩ := hC χS χT ω hω μ 𝓕 hcov f hfU

  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A, A, fun h => ?_⟩
  have key := hbd g h
  unfold thetaKO
  calc ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := key
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A * height W h ^ A := by
      rw [mul_pow]; ring

theorem integrableOn_of_rapidDec (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) {F : GA D W → ℂ} (hF : RapidDec W F) (g : GA D V) :
    IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν := by
  have hcont := thetaKO_continuous hω hf g
  exact hF.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth hG hθ hω hf g)
    (thetaKO_left hω hf g) hcont.aestronglyMeasurable


end GlobalTheory.Chain.LiftConv
