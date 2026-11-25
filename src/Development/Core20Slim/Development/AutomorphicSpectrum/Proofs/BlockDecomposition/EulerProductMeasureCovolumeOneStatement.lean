module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureCovolumeOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) → ∀ (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ G : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (hypOne J), Ψinf (actW (Ainf F) σ (hypOne J) g (e0 _ M)) = stageInt (Ainf F) σ J b laminf minf φinf g) → (∀ v, ∀ g : HA (Fv F v) σ (hypOne J), Ψ v (actW (Fv F v) σ (hypOne J) g (e0 _ M)) = stageInt (Fv F v) σ J b (lam v) (m v) (φ v) g) → (∀ v, ∀ g : HA (Fv F v) σ (hypOne J), G v (actW (Fv F v) σ (hypOne J) g (e0 _ M)) = stageInt (Fv F v) σ J b (lam v) (m v) ((latV b v).indicator 1) g) → ∀ h : HA (AF F) σ (hypOne J), ∃ Sh : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ Sh ∧ ∀ S', Sh ⊆ S' → ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂I = ENNReal.ofReal (∏' v : {v // v ∉ S'}, (m v.1 (latV b v.1)).toReal) * purePr σ J b S' Ψinf (fun v => if v ∈ S then Ψ v else G v) (actW (AF F) σ (hypOne J) h (e0 _ M)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure.inner_pure | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure.inner_pure | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure.inner_pure <;> assumption)
