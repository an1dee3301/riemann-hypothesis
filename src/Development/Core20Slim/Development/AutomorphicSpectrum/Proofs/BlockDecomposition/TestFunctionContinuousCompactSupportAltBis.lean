module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestTContinuousHasCompactSupport
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_and_hasCompactSupport_testT : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) → Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧ HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport <;> assumption)
