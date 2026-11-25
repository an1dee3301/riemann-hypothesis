module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.Core20Slim.Development.WeilBound.CoreStatements.ThetaDilations.EulerMove
public import Development.Core20Slim.Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Action
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
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
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

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def scalH (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) : HermR R σ n :=
  ⟨(algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h : sigR R σ (algebraMap R (R ⊗[F] E) l) = algebraMap R (R ⊗[F] E) l := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h, S.2 a b]⟩

theorem scalH_coe (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) :
    (scalH R σ l S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl

theorem scalH_hermScal (σ : E →ₐ[F] E) (l s : R) :
    scalH R σ l (hermScal R σ s) = hermScal R σ (l * s) := by
  apply Subtype.ext
  funext a b
  change (algebraMap R (R ⊗[F] E) l) * (s ⊗ₜ[F] (1 : E)) = (l * s) ⊗ₜ[F] (1 : E)
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

end Alg

theorem euler_move_c : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → ∀ κ : ℝ≥0, IsEulerProd b I κ minf m → IsEulerProd b (I.map e) κ minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf κ hE
  have tr : ∀ (J : Measure (Fin n → Fin M → AF F ⊗[F] E)) (a : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (w : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsEulerProd b J κ a w ↔ IsEulerProd b J 1 (κ • a) w := fun J a w => by
    have e1 : ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, ∫⁻ X, φ X ∂(κ • a) = (κ : ℝ≥0∞) * ∫⁻ X, φ X ∂a := fun φ => by
      rw [ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
    simp only [IsEulerProd, e1, ENNReal.coe_one, one_mul, mul_assoc]
  rw [tr] at hE ⊢
  refine PositivityTheory.PlacePermOperatorBicommutantSpan.euler_move F E σ hcm d b n M I _ _ m m' e ei ev me mei mev hpr hG ci c hc ?_ h2 hf hE
  rw [Measure.map_smul κ mei.aemeasurable, h1, smul_comm]

end GlobalTheory.CompanionTheory.SW.MassSimil

end
