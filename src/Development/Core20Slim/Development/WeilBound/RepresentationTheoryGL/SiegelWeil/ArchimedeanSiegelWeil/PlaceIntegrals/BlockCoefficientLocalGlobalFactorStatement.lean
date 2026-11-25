module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactor
public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
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
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
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
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
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

theorem _root_.GlobalTheory.T.block_coefficient_local_global_factor : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral | exact GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral
