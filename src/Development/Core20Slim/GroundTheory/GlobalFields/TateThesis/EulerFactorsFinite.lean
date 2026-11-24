module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeLFunction
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite

@[expose] public section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
  MeasureTheory WithZero
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem count_coeIdeal_eq_multiplicity (v : HeightOneSpectrum (𝓞 K)) {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) :
    FractionalIdeal.count K v (𝔪 : FractionalIdeal (𝓞 K)⁰ K) = multiplicity v.asIdeal 𝔪 := by
  have h0 : 𝔪 ≠ 0 := h𝔪
  rw [FractionalIdeal.count_coe K v h0, Ideal.count_associates_factors_eq h0 v.isPrime v.ne_bot,
    count_normalizedFactors_eq_multiplicity h𝔪]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)




open Classical in
def finiteTest (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : ℂ :=
  if v.asIdeal ∣ χ.conductor then
    (if h : Valued.v x = 1 then
      (((χ.localComponent v (Units.mk0 x fun h0 ↦ by simp [h0] at h))⁻¹ : Circle) : ℂ) else 0)
  else if Valued.v x ≤ 1 then 1 else 0

def finiteTestFun (x : FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏ᶠ v, χ.finiteTest v (x v)





























end HeckeCharacter

end

end GroundTheory.Global
