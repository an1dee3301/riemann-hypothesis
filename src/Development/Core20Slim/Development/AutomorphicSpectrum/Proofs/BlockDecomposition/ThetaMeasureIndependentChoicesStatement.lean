module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoices
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.Core20Slim.Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.Core20Slim.Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_independent_choices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | exact GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep <;> assumption)
