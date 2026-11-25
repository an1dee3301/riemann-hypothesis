module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
public import Development.Core20Slim.GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding IdeleGroup
open scoped NumberField.LiesOver

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_infiniteEmbedding (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ideleNorm K K' (infiniteEmbedding v' a) =
      infiniteEmbedding (v'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_infiniteEmbedding]
    by_cases hw : w = v'.comap (algebraMap K K')
    · subst hw
      rw [Finset.prod_eq_single (⟨v', (inferInstance : v'.LiesOver (v'.comap (algebraMap K K')))⟩ :
          (v'.comap (algebraMap K K')).placesOver K'),
        infiniteAdeleSingle_apply, infiniteAdeleSingle_apply, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_same, LocalField.coe_normUnits]
      · intro u _ hu
        rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)),
          map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw]
      refine Finset.prod_eq_one fun u _ ↦ ?_
      have hu : (u : InfinitePlace K') ≠ v' := by
        rintro h
        apply hw
        rw [← h]
        exact ((GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq w _).1 u.2).symm
      rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu, map_one]
  · rw [ideleNorm_snd]
    exact Finset.prod_eq_one fun _ _ ↦ map_one _

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in
theorem restrictNormal_restrictScalars_conjAt [IsGalois K L] [IsGalois K' L']
    (u' : InfinitePlace L') (hv : (u'.comap (algebraMap K' L')).IsReal) :
    ((conjAt K' u').restrictScalars K).restrictNormal L = conjAt K (u'.comap (algebraMap L L')) := by
  have h := isConj_conjAt_of_isReal L' hv
  have hr : IsConj (u'.embedding.comp (algebraMap L L'))
      (((conjAt K' u').restrictScalars K).restrictNormal L) := by
    rw [isConj_iff_forall]
    intro l
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.restrictScalars_apply]
    exact h.eq _
  have hmk : mk (u'.embedding.comp (algebraMap L L')) =
      mk (u'.comap (algebraMap L L')).embedding := by
    rw [mk_embedding, ← comap_mk, mk_embedding]
  exact (conjOfEmbedding_eq ((isConj_iff_of_mk_eq hmk _).1 hr)).symm

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]


omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')] in
theorem restrictNormal_restrictScalars_one [Normal K L] :
    ((1 : L' ≃ₐ[K'] L').restrictScalars K).restrictNormal L = 1 := by
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.one_apply,
    AlgEquiv.one_apply]


omit [NumberField K] [NumberField K'] in
theorem extensionEmbeddingOfIsReal_normUnits (v' : InfinitePlace K') (hv' : v'.IsReal)
    (a : v'.Completionˣ) :
    extensionEmbeddingOfIsReal (hv'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a : _) =
      extensionEmbeddingOfIsReal hv' a := by
  have hv := hv'.comap (algebraMap K K')
  have hfin : Module.finrank (v'.comap (algebraMap K K')).Completion v'.Completion = 1 :=
    (GroundTheory.Global.InfinitePlace.finrank_completion_eq_one_iff v').2
      fun h ↦ not_isComplex_iff_isReal.2 hv' h.2
  obtain ⟨c, hc⟩ := ((Algebra.finrank_eq_one_iff_bijective_algebraMap).1 hfin).2
    (a : v'.Completion)
  have e1 : (extensionEmbeddingOfIsReal hv'
      (algebraMap (v'.comap (algebraMap K K')).Completion v'.Completion c) : ℂ) =
        extensionEmbeddingOfIsReal hv c := by
    rw [extensionEmbeddingOfIsReal_apply]
    exact GroundTheory.Global.InfinitePlace.extensionEmbedding_algebraMap hv c
  rw [LocalField.coe_normUnits, ← hc, Algebra.norm_algebraMap, hfin, pow_one]
  exact (Complex.ofReal_injective e1).symm

theorem restrictNormal_infiniteLocalSymbol_norm (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ((infiniteLocalSymbol L' v' a).restrictScalars K).restrictNormal L =
      infiniteLocalSymbol L (v'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  by_cases hv' : v'.IsReal
  · have hv := hv'.comap (algebraMap K K')
    obtain ⟨u'⟩ := IdeleNorm.nonempty_infinitePlacesOver (L := L') v'
    have hu'v' : (u' : InfinitePlace L').comap (algebraMap K' L') = v' :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v' _).1 u'.2
    have hu : ((u' : InfinitePlace L').comap (algebraMap L L')).LiesOver
        (v'.comap (algebraMap K K')) :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq _ _).2 (by
        rw [← comap_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq K K' L',
          comap_comp, hu'v'])
    rw [infiniteLocalSymbol_apply L' v' hv' u', infiniteLocalSymbol_apply L _ hv ⟨_, hu⟩,
      extensionEmbeddingOfIsReal_normUnits v' hv' a]
    split_ifs
    · exact restrictNormal_restrictScalars_conjAt (u' : InfinitePlace L') (by rw [hu'v']; exact hv')
    · exact restrictNormal_restrictScalars_one
  · rw [infiniteLocalSymbol_of_not_isReal L' v' hv', MonoidHom.one_apply,
      restrictNormal_restrictScalars_one]
    by_cases hv : (v'.comap (algebraMap K K')).IsReal
    · obtain ⟨u⟩ := IdeleNorm.nonempty_infinitePlacesOver (L := L) (v'.comap (algebraMap K K'))
      rw [infiniteLocalSymbol_apply L _ hv u, if_neg]
      rw [not_lt, LocalField.coe_normUnits, GroundTheory.Global.InfinitePlace.extensionEmbeddingOfIsReal_norm
        hv (not_isReal_iff_isComplex.1 hv')]
      exact Complex.normSq_nonneg _
    · rw [infiniteLocalSymbol_of_not_isReal L _ hv, MonoidHom.one_apply]

end

end GroundTheory.Global
