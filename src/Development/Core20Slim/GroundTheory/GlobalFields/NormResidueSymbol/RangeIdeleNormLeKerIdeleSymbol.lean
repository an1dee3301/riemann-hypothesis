module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Abstract
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

abbrev galCommGroup : CommGroup (L ≃ₐ[K] L) :=
  { toGroup := (inferInstance : Group (L ≃ₐ[K] L)), mul_comm := mul_comm' }

attribute [local instance] galCommGroup

def ideleSymbol : IdeleGroup K →* (L ≃ₐ[K] L) :=
  IdeleMap.ideleMap (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)

variable {K}

theorem ideleSymbol_apply (x : IdeleGroup K) :
    ideleSymbol K L x = (∏ᶠ v, localSymbol L v (finiteProj v x)) *
      ∏ w, infiniteLocalSymbol L w (infiniteProj w x) :=
  IdeleMap.ideleMap_apply (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) x

theorem hasFiniteMulSupport_localSymbol (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ localSymbol L v (finiteProj v x) :=
  IdeleMap.hasFiniteMulSupport (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v)
    (eventually_units_le_ker_localSymbol L) x

@[simp]
theorem ideleSymbol_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleSymbol K L (finiteEmbedding v a) = localSymbol L v a :=
  IdeleMap.ideleMap_finiteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) v a

@[simp]
theorem ideleSymbol_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleSymbol K L (infiniteEmbedding w a) = infiniteLocalSymbol L w a :=
  IdeleMap.ideleMap_infiniteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) w a

theorem continuous_ideleSymbol : Continuous (ideleSymbol K L) :=
  IdeleMap.continuous_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w)


theorem eq_ideleSymbol {ψ : IdeleGroup K →* (L ≃ₐ[K] L)} (hψ : Continuous ψ)
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = localSymbol L v a)
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = infiniteLocalSymbol L w a) :
    ψ = ideleSymbol K L :=
  IdeleMap.eq_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w) hψ
    (fun v ↦ MonoidHom.ext (hfin v)) (fun w ↦ MonoidHom.ext (hinf w))

theorem range_ideleNorm_le_ker_ideleSymbol : (ideleNorm K L).range ≤ (ideleSymbol K L).ker := by
  intro x hx
  obtain ⟨hf, hi⟩ := (IdeleNorm.mem_range_ideleNorm_iff_forall L x).1 hx
  exact IdeleMap.ideleMap_eq_one_of_forall_mem (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)
    (fun v ↦ (IdeleNorm.finiteLocalNorm L v).range)
    (fun w ↦ (IdeleNorm.infiniteLocalNorm L w).range)
    (fun v ↦ range_finiteLocalNorm_le_ker_localSymbol L v)
    (fun w ↦ range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L w) hf hi

@[simp]
theorem ideleSymbol_ideleNorm (y : IdeleGroup L) : ideleSymbol K L (ideleNorm K L y) = 1 :=
  range_ideleNorm_le_ker_ideleSymbol L ⟨y, rfl⟩

end

end GroundTheory.Global
