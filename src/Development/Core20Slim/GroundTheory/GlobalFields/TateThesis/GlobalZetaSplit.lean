module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

@[expose] public section

open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def partialZetaSum (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  ∑' ξ : Kˣ, f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
    (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ)

theorem partialZetaSum_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) {δ : normOneSubgroup K}
    (hδ : δ ∈ diagonalNormOne K) : partialZetaSum w f χ t (u * δ) = partialZetaSum w f χ t u := by
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hδ
  obtain ⟨ξ₀, hξ₀⟩ := hδ
  unfold partialZetaSum
  conv_rhs => rw [← (Equiv.mulRight ξ₀).tsum_eq]
  refine tsum_congr fun ξ ↦ ?_
  have hχ : χ.toIdele (moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [Subgroup.coe_mul, ← hξ₀, ← mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]
  have hf : diagonal K ξ * moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K) =
      diagonal K ((Equiv.mulRight ξ₀) ξ) * moduleSection w t * (u : IdeleGroup K) := by
    rw [Subgroup.coe_mul, ← hξ₀, Equiv.coe_mulRight, map_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [hχ, hf]

def partialZetaClass (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : normOneSubgroup K ⧸ diagonalNormOne K → ℂ :=
  Quotient.lift (s := QuotientGroup.leftRel (diagonalNormOne K)) (partialZetaSum w f χ t)
    fun u v h ↦ by
      have h' : u⁻¹ * v ∈ diagonalNormOne K := QuotientGroup.leftRel_apply.1 h
      conv_rhs => rw [← mul_inv_cancel_left u v]
      rw [partialZetaSum_mul w f χ t u h']

def partialZeta (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ c, partialZetaClass w f χ t c ∂normOneClassMeasure K

theorem measurable_partialZetaSum (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) : Measurable (partialZetaSum w f χ t) := by
  refine Measurable.tsum fun ξ ↦ Continuous.measurable ?_
  have hu : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have hu' : Continuous fun u : normOneSubgroup K ↦
      diagonal K ξ * moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  exact (hf.comp (Units.continuous_val.comp hu')).mul
    (continuous_subtype_val.comp (χ.continuous_toIdele.comp hu))

theorem partialZeta_eq_setIntegral (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    partialZeta w f χ t =
      ∫ u in normOneFundamentalDomain K, partialZetaSum w f χ t u ∂normOneMeasure K := by
  have hm : Measurable (partialZetaClass w f χ t) :=
    QuotientGroup.measurable_from_quotient.2 (measurable_partialZetaSum w hf χ t)
  rw [partialZeta, normOneClassMeasure,
    integral_map QuotientGroup.measurable_coe.aemeasurable hm.aestronglyMeasurable]
  rfl



end

end GroundTheory.Global
