module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap

@[expose] public section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Matrix Filter
  Topology
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]











def localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  Circle.toUnits.comp (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle)

@[simp]
theorem coe_localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : ((localChar χ v a : ℂˣ) : ℂ) = (χ.localComponent v a : ℂ) :=
  rfl

theorem continuous_localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localChar χ v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_subtype_val.comp (χ.localComponent v).continuous
  · have h : (fun a ↦ (((localChar χ v a)⁻¹ : ℂˣ) : ℂ)) =
        fun a ↦ ((χ.localComponent v a⁻¹ : Circle) : ℂ) := by
      funext a
      rw [← map_inv, coe_localChar]
    rw [h]
    exact continuous_subtype_val.comp ((χ.localComponent v).continuous.comp continuous_inv)












end

end GroundTheory.Automorphic.GodementSection
