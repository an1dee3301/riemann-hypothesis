module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZetaSplit
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def adelicTheta (F : 𝔸[K] → ℂ) (a : IdeleGroup K) : ℂ :=
  ∑' ξ : K, F (a • algebraMap K 𝔸[K] ξ)




theorem smul_algebraMap_zero (a : IdeleGroup K) : a • algebraMap K 𝔸[K] 0 = 0 := by
  rw [map_zero, smul_zero]

theorem continuousOn_adelicTheta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) : ContinuousOn (adelicTheta F) C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap hF hC
  refine continuousOn_tsum (fun ξ ↦ ?_) hu (fun ξ a ha ↦ hFu a ha ξ)
  have h : Continuous fun a : IdeleGroup K ↦ F ((a : 𝔸[K]) * algebraMap K 𝔸[K] ξ) :=
    (continuous_of_mem_schwartzBruhat hF).comp (Units.continuous_val.mul continuous_const)
  exact h.continuousOn

theorem continuous_adelicTheta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Continuous (adelicTheta F) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  obtain ⟨C, hC, haC⟩ := exists_compact_mem_nhds a
  exact (continuousOn_adelicTheta hF hC).continuousAt haC











def thetaIntegrand (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  adelicTheta F (moduleSection w t * (u : IdeleGroup K)) * (χ.toIdele (u : IdeleGroup K) : ℂ)

def thetaIntegral (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain K, thetaIntegrand w F χ t u ∂normOneMeasure K


theorem continuous_thetaIntegrand (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    Continuous (thetaIntegrand w F χ t) := by
  have h1 : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have h2 : Continuous fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ) :=
    continuous_subtype_val.comp (χ.continuous_toIdele.comp continuous_subtype_val)
  exact ((continuous_adelicTheta hF).comp h1).mul h2

theorem integrableOn_thetaIntegrand (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    IntegrableOn (thetaIntegrand w F χ t) (normOneFundamentalDomain K) (normOneMeasure K) :=
  ((continuous_thetaIntegrand w hF χ t).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure

theorem integrableOn_char (χ : HeckeCharacter K) :
    IntegrableOn (fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ))
      (normOneFundamentalDomain K) (normOneMeasure K) :=
  ((continuous_subtype_val.comp (χ.continuous_toIdele.comp
    continuous_subtype_val)).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure

theorem toIdele_inv (χ : HeckeCharacter K) (x : IdeleGroup K) :
    (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl




end

end GroundTheory.Global
