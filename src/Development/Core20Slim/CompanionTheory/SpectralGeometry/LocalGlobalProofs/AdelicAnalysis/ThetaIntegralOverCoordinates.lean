module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegativeStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.PullCoord

theorem lintegral_thetaMeas_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ 𝓕 hμ h𝓕 S T hST Φ hΦ
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ 𝓕 hμ h𝓕 1 T Φ hΦ]
  have hb := RatCoord.ofF_bijective (M := M) b
  let e : S ≃ T := Equiv.ofBijective (fun x => ⟨ofF b x.1, (hST x.1).2 x.2⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hb.1 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y.1
      exact ⟨⟨x, (hST x).1 (hx ▸ y.2)⟩, Subtype.ext hx⟩)
  have hsum : ∀ h : HA (AF F) σ J,
      ∑' X : T, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))
        = ∑' x : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (ofF b x.1))) := fun h =>
    (e.tsum_eq (fun X : T =>
      Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E))))).symm
  simp only [hsum, prH, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.SW.BB.PullCoord
