module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentFundamentalDomainLayersIntegralStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldNormBaseTermTranslate
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrbitSumModerateGrowth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseTermNormCoords
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.UnfoldBound


set_option maxHeartbeats 1000000 in
theorem unfolded_integral_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * height V g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨vN⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.1 V V₀ ρ d
  obtain ⟨𝓐, h𝓐, hlay⟩ := GlobalTheory.T.flagUnipotent_fundamentalDomain_layers_integral D V V₀ ρ d vN vb vU
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.orbit_sum_moderate_growth D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ G Φ hG hΦ
  refine ⟨C, A, fun g => ?_⟩
  exact ((GlobalTheory.Unf.base_term_norm_coords D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ G Φ hG hΦ 𝓐 𝓑 hlay g).trans
    (GlobalTheory.Unf.unfold_norm_base_term_translate D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑
      g)).le.trans (hC g)

end GlobalTheory.Unf.UnfoldBound

end
