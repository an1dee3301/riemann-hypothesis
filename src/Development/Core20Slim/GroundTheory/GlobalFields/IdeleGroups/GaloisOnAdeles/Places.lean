module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

theorem adeleRingEquiv_eq_adeleMap (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) :
    (adeleRingEquiv τ : 𝔸[L] →+* 𝔸[L']) = adeleMap L L' := by
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · rw [RingHom.coe_coe, adeleRingEquiv_algebraMap, adeleMap_algebraMap, hτ]
  · rw [RingHom.coe_coe, adeleRingEquiv_adeleMap_rat, adeleMap_adeleMap]

theorem adeleRingEquiv_snd (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) (x : 𝔸[L])
    (w' : HeightOneSpectrum (𝓞 L')) :
    (adeleRingEquiv τ x).2 w' = SemiLocal.completionMap (below L w') w' (x.2 (below L w')) := by
  rw [← RingHom.coe_coe, adeleRingEquiv_eq_adeleMap τ hτ]
  rfl

theorem adeleRingEquiv_fst (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) (x : 𝔸[L])
    (w' : InfinitePlace L') :
    (adeleRingEquiv τ x).1 w' =
      algebraMap (w'.comap (algebraMap L L')).Completion w'.Completion
        (x.1 (w'.comap (algebraMap L L'))) := by
  rw [← RingHom.coe_coe, adeleRingEquiv_eq_adeleMap τ hτ]
  rfl

theorem completionMap_below_algebraMap (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l)
    (w' : HeightOneSpectrum (𝓞 L')) (l : L) :
    SemiLocal.completionMap (below L w') w' (algebraMap L ((below L w').adicCompletion L) l) =
      algebraMap L' (w'.adicCompletion L') (τ l) := by
  rw [SemiLocal.completionMap_algebraMap, hτ, IsScalarTower.algebraMap_apply L L']


omit [NumberField L] [NumberField L'] in
theorem completion_algebraMap_comap_apply (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l)
    (w' : InfinitePlace L') (l : L) :
    algebraMap (w'.comap (algebraMap L L')).Completion w'.Completion
        (algebraMap L (w'.comap (algebraMap L L')).Completion l) =
      algebraMap L' w'.Completion (τ l) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply L L', hτ]

variable {M M' : Type*} [Field M] [NumberField M] [Field M'] [NumberField M']

def comapPrime (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) : HeightOneSpectrum (𝓞 M) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  below M w'

omit [NumberField M] [NumberField M'] in
theorem comapPrime_asIdeal (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    (comapPrime τ w').asIdeal = w'.asIdeal.comap (RingOfIntegers.mapRingHom (τ : M →+* M')) :=
  rfl

def finiteCompletionMap (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    (comapPrime τ w').adicCompletion M →+* w'.adicCompletion M' :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  SemiLocal.completionMap (below M w') w'

theorem finiteCompletionMap_algebraMap (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) (l : M) :
    finiteCompletionMap τ w' (algebraMap M _ l) = algebraMap M' (w'.adicCompletion M') (τ l) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  completionMap_below_algebraMap τ (fun _ ↦ rfl) w' l

def infiniteCompletionMap (τ : M ≃+* M') (w' : InfinitePlace M') :
    (w'.comap (τ : M →+* M')).Completion →+* w'.Completion :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion


omit [NumberField M] [NumberField M'] in
theorem infiniteCompletionMap_algebraMap (τ : M ≃+* M') (w' : InfinitePlace M') (l : M) :
    infiniteCompletionMap τ w' (algebraMap M _ l) = algebraMap M' w'.Completion (τ l) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  completion_algebraMap_comap_apply τ (fun _ ↦ rfl) w' l

theorem adeleRingEquiv_snd_eq (τ : M ≃+* M') (x : 𝔸[M]) (w' : HeightOneSpectrum (𝓞 M')) :
    (adeleRingEquiv τ x).2 w' = finiteCompletionMap τ w' (x.2 (comapPrime τ w')) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  adeleRingEquiv_snd τ (fun _ ↦ rfl) x w'

theorem adeleRingEquiv_fst_eq (τ : M ≃+* M') (x : 𝔸[M]) (w' : InfinitePlace M') :
    (adeleRingEquiv τ x).1 w' = infiniteCompletionMap τ w' (x.1 (w'.comap (τ : M →+* M'))) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  adeleRingEquiv_fst τ (fun _ ↦ rfl) x w'

section Galois

variable {K : Type*} [Field K] [NumberField K] [Algebra K M]


omit [NumberField K] [NumberField M] in
theorem comapPrime_eq_inv_smul (σ : M ≃ₐ[K] M) (w' : HeightOneSpectrum (𝓞 M)) :
    comapPrime (σ : M ≃+* M) w' = σ⁻¹ • w' := by
  ext1
  rw [comapPrime_asIdeal, SemiLocal.smul_asIdeal, Ideal.pointwise_smul_eq_comap]
  ext y
  simp only [Ideal.mem_comap]
  constructor <;> intro h <;> convert h using 2 <;> ext <;> rfl


omit [NumberField K] [NumberField M] in
theorem comap_eq_inv_smul (σ : M ≃ₐ[K] M) (w' : InfinitePlace M) :
    w'.comap ((σ : M ≃+* M) : M →+* M) = σ⁻¹ • w' := by
  ext y
  rw [InfinitePlace.comap_apply, InfinitePlace.smul_apply]
  rfl


omit [NumberField K] in
theorem smul_snd (σ : M ≃ₐ[K] M) (x : 𝔸[M]) (w' : HeightOneSpectrum (𝓞 M)) :
    (σ • x).2 w' = finiteCompletionMap (σ : M ≃+* M) w' (x.2 (comapPrime (σ : M ≃+* M) w')) :=
  adeleRingEquiv_snd_eq _ x w'


omit [NumberField K] in
theorem smul_fst (σ : M ≃ₐ[K] M) (x : 𝔸[M]) (w' : InfinitePlace M) :
    (σ • x).1 w' = infiniteCompletionMap (σ : M ≃+* M) w' (x.1 (w'.comap ((σ : M ≃+* M) : M →+* M))) :=
  adeleRingEquiv_fst_eq _ x w'

end Galois

end AdeleBaseChange

end

end GroundTheory.Global
