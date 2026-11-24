module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowConv

theorem thetaKO_toSgn {D : D7} {S T : HSp D} (om : GlobalTheory.Grid.WRep S T) (h : GA D S) (g : GA D T) (f : WO S T → ℂ) :
    thetaKO om h g f = thetaKO (om.toSgn true) ((GlobalTheory.Grid.ofSgn true S).symm h) g f := by
  unfold thetaKO GlobalTheory.Grid.WRep.toSgn
  simp

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    ∀ γ ∈ GQ T, ∀ g, thetaKO om h (γ * g) f = thetaKO om h g f := fun γ hγ g => by
  have e : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) _ hγ _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    Continuous fun g => thetaKO om h g f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_right h)

theorem conj_thetaKO_modGrowth_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    GlobalTheory.Grow.ModGrowth T fun g => conj (thetaKO om h g f) := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ S T χS χT om hω f hf
  refine ⟨C * GlobalTheory.Grow.height S h ^ A, A, fun g => ?_⟩
  rw [RCLike.norm_conj, mul_assoc, ← mul_pow]
  exact hC h g

theorem conj_thetaKO_mul_integrableOn (hP : GlobalTheory.Published.CuspRapidDecay)
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Ainf ↥D.host.F) D.host.E →+* ℂ} (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ)
    (hc : IsCuspFun T φ) (h : GA D S) :
    IntegrableOn (fun g => conj (thetaKO om h g f) * φ g) 𝓕 ν :=
  (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc).integrableOn_modGrowth_mul hν h𝓕
    (conj_thetaKO_modGrowth_snd hω hf h)
    (fun γ hγ g => by simp only [thetaKO_left_snd hω hf h γ hγ g])
    ((Complex.continuous_conj.comp (thetaKO_continuous_snd hω hf h)).measurable.aestronglyMeasurable)

end GlobalTheory.UpArrowConv
