module

public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormulaStatement
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilFreeOfBlockNonemptyFramesStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalizationStatement
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactorStatement
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

theorem siegel_frame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ hH t β hNF hx
  obtain ⟨hr, hψ, hθ, hμ, hlam, hν, hφ, habs⟩ := id hH
  obtain ⟨x, hxr, hxg⟩ := hx
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hν
  have hfr : (framesE D.sp.cm.sig V.gram β.1).Nonempty := by
    refine ⟨fun a i => x i a, ?_⟩
    rw [trM_mem_framesE_iff]
    exact ⟨hxr, hxg⟩
  obtain ⟨d, b, laminf, lamv, minf, m, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_tamagawa_measure_normalization D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r
  have hS := GlobalTheory.T.siegelWeil_free_of_block_nonempty_frames D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r t β.1 (hermE_symm β) hNF hr hfr
    d b laminf lamv h1 h2 ν 𝓕 hν h𝓕 minf m h3 h4
  obtain ⟨hi, he⟩ := GlobalTheory.T.frame_integral_theta_measure_formula D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  rw [he]
  exact (GlobalTheory.T.block_coefficient_local_global_factor D r V ψ θ μ lam ν φ hH t β hNF d b laminf lamv minf m h1 h2 h3 h4 _ hS hi).symm

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
