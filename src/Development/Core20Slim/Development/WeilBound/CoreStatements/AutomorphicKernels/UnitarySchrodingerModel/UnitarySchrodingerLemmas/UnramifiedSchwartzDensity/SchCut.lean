module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace PositivityTheory.PfSWUS.SchInf

open GlobalTheory.CompanionTheory.SW

def FamCont : Prop :=
  ∀ (N : ℕ) (X : Type) [TopologicalSpace X] (μ' : Measure (Fin N → ℝ)), μ'.IsAddHaarMeasure →
  ∀ (n : X → Measure (Fin N → ℝ)) (c : X) (O : Set X), IsOpen O → c ∈ O →
  (∀ f : (Fin N → ℝ) → ℝ≥0∞, Measurable f → ∫⁻ y, f y ∂μ' ≠ ⊤ →
      ∀ U : Set X, IsOpen U → U.Nonempty → ∃ s ∈ U, ∫⁻ y, f y ∂(n s) ≠ ⊤) →
  (∀ s₀ ∈ O, ∃ (L Linv : X → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (Λ : X → ℝ≥0),
      ContinuousAt L c ∧ ContinuousAt Linv c ∧ ContinuousAt Λ c ∧
      (∀ s ∈ O, ∀ y, Linv s (L s y) = y) ∧ ∀ s ∈ O, n s = Λ s • (n s₀).map (L s)) →
  ∀ g : (Fin N → ℝ) → ℂ, Continuous g → (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) →
    (∀ᶠ s in 𝓝 c, Integrable g (n s)) ∧ ContinuousAt (fun s => ∫ y, g y ∂(n s)) c

def SecInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n : ℕ) (c : HermR (Ainf F) σ n), IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
  ∃ O : Set (HermR (Ainf F) σ n), IsOpen O ∧ c ∈ O ∧ ∀ S₀ ∈ O,
    ∃ h hinv : HermR (Ainf F) σ n → Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      ContinuousOn h O ∧ ContinuousOn hinv O ∧
      ∀ S ∈ O, h S * hinv S = 1 ∧ hinv S * h S = 1 ∧
        (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
          cT (sigR (Ainf F) σ) (h S) * (S₀ : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h S

def CoordInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n M : ℕ), ∃ (N : ℕ) (eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous eV ∧ Continuous eV.symm ∧
    ∃ L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ), Continuous L ∧
      ∀ g X, eV (rmul (Ainf F) X g) = L g (eV X)

def ScaleInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
  ∃ A C : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → ℝ≥0,
    ContinuousOn A {g | IsUnit g.det} ∧ ContinuousOn C {g | IsUnit g.det} ∧
    ∀ g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E), IsUnit g.det →
      A g ≠ 0 ∧ C g ≠ 0 ∧ μ.map (fun X => rmul (Ainf F) X g) = A g • μ ∧
      ∀ τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n,
        (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) g * S * g) → ν.map τ = C g • ν

def FinOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n))
    (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m →
  ∀ f : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ X, f X ∂μ ≠ ⊤ →
  ∀ U : Set (HermR (Ainf F) σ n), IsOpen U → U.Nonempty → ∃ S ∈ U, ∫⁻ X, f X ∂(m S) ≠ ⊤

def DensInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n))
    (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m →
  ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ →
    (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) →
    ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} →
  ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} →
    ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν

end PositivityTheory.PfSWUS.SchInf

end
