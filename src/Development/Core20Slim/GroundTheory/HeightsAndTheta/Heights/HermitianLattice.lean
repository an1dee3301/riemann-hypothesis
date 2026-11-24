module

public import Mathlib

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct

noncomputable section

def ComplexAt {K : Type*} [Field K] (_σ : K →+* ℂ) : Type := ℂ

namespace ComplexAt

variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)

instance : CommRing (ComplexAt σ) := inferInstanceAs (CommRing ℂ)

instance : Algebra ℂ (ComplexAt σ) := inferInstanceAs (Algebra ℂ ℂ)

def ofComplex : ℂ ≃ₐ[ℂ] ComplexAt σ := AlgEquiv.refl

instance : Algebra (𝓞 K) (ComplexAt σ) :=
  ((ofComplex σ).toRingHom.comp (σ.comp (algebraMap (𝓞 K) K))).toAlgebra

theorem smul_def (a : 𝓞 K) (z : ComplexAt σ) : a • z = ofComplex σ (σ (a : K)) * z := rfl

theorem complex_smul_def (c : ℂ) (z : ComplexAt σ) : c • z = ofComplex σ c * z := rfl

instance : SMulCommClass (𝓞 K) ℂ (ComplexAt σ) where
  smul_comm a c z := by
    rw [smul_def, complex_smul_def, complex_smul_def, smul_def, mul_left_comm]

def conj : ComplexAt σ →+* ComplexAt (conjugate σ) :=
  (ofComplex (conjugate σ)).toRingHom.comp ((starRingEnd ℂ).comp (ofComplex σ).symm.toRingHom)

theorem conj_ofComplex (z : ℂ) :
    conj σ (ofComplex σ z) = ofComplex (conjugate σ) (starRingEnd ℂ z) := rfl

def conjLinear : ComplexAt σ →ₗ[𝓞 K] ComplexAt (conjugate σ) where
  toFun := conj σ
  map_add' := map_add _
  map_smul' a z := by
    rw [smul_def, map_mul, RingHom.id_apply, smul_def, conj_ofComplex]
    rfl


end ComplexAt

open ComplexAt

variable {K : Type*} [Field K]

abbrev Fibre (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] : Type _ :=
  ComplexAt σ ⊗[𝓞 K] E

section Fibre

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

def conjMap : Fibre σ E →ₗ[𝓞 K] Fibre (conjugate σ) E :=
  TensorProduct.map (conjLinear σ) LinearMap.id

variable {σ E}

@[simp]
theorem conjMap_tmul (z : ComplexAt σ) (e : E) : conjMap σ E (z ⊗ₜ e) = conj σ z ⊗ₜ e := rfl


end Fibre

structure HermitianMetric (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] where

  form : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ E)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fibre σ E),
    (form (conjugate σ)).inner (conjMap σ E x) (conjMap σ E y) = starRingEnd ℂ ((form σ).inner x y)

structure HermitianBundle.{u} (K : Type*) [Field K] [NumberField K] where

  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module (𝓞 K) carrier]
  [instFinite : Module.Finite (𝓞 K) carrier]
  [instProjective : Module.Projective (𝓞 K) carrier]

  metric : HermitianMetric K carrier

attribute [instance] HermitianBundle.instAddCommGroup HermitianBundle.instModule
  HermitianBundle.instFinite HermitianBundle.instProjective

@[instance_reducible]
def coreOfInjective {𝕜 V W : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (f : V →ₗ[𝕜] W)
    (hf : Function.Injective f) : InnerProductSpace.Core 𝕜 V where
  inner x y := inner 𝕜 (f x) (f y)
  conj_inner_symm x y := inner_conj_symm (f x) (f y)
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by simp only [map_add (f := _), inner_add_left]
  smul_left x y r := by simp only [map_smul, inner_smul_left]
  definite x h := hf (by rw [map_zero]; exact inner_self_eq_zero.mp h)


section Examples

variable (K : Type*) [Field K] [NumberField K]


variable {K}



variable (K)




variable {K}



variable (K)





end Examples








end

end GroundTheory.Heights₂.Heights
