module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.Splitting
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField SemiLocal AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_finiteEmbedding (v' : HeightOneSpectrum (𝓞 K')) (a : (v'.adicCompletion K')ˣ) :
    ideleNorm K K' (finiteEmbedding v' a) =
      finiteEmbedding (below K v')
        (LocalField.normUnits ((below K v').adicCompletion K) (v'.adicCompletion K') a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_finiteEmbedding]
    exact (Finset.prod_eq_one fun _ _ ↦ map_one _)
  · rw [ideleNorm_snd]
    simp only [coe_finiteEmbedding]
    by_cases hv : v = below K v'
    · subst hv
      rw [Finset.prod_eq_single (⟨v', inferInstance⟩ : PlacesOver K' (below K v')),
        finiteAdeleSingle_apply_self, finiteAdeleSingle_apply_self, LocalField.coe_normUnits]
      · intro w _ hw
        rw [finiteAdeleSingle_apply_of_ne (fun h ↦ hw (Subtype.ext h)), map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [finiteAdeleSingle_apply_of_ne hv]
      refine Finset.prod_eq_one fun w _ ↦ ?_
      have hw : w.1 ≠ v' := by
        rintro h
        apply hv
        rw [← h]
        exact ((below_eq_iff w.1 v).2 w.2).symm
      rw [finiteAdeleSingle_apply_of_ne hw, map_one]

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


omit [NumberField K] [NumberField K'] [NumberField L'] in
theorem liesOver_trans_of_liesOver (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K'))
    (u' : HeightOneSpectrum (𝓞 L')) [v'.asIdeal.LiesOver v.asIdeal]
    [u'.asIdeal.LiesOver v'.asIdeal] : u'.asIdeal.LiesOver v.asIdeal :=
  (below_eq_iff u' v).1 (by
    rw [← below_below (L := K'), (below_eq_iff u' v').2 inferInstance,
      (below_eq_iff v' v).2 inferInstance])

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_localSymbol_norm (v : HeightOneSpectrum (𝓞 K))
    (v' : HeightOneSpectrum (𝓞 K')) [v'.asIdeal.LiesOver v.asIdeal] (a : (v'.adicCompletion K')ˣ) :
    ((localSymbol L' v' a).restrictScalars K).restrictNormal L =
      localSymbol L v (LocalField.normUnits (v.adicCompletion K) (v'.adicCompletion K') a) := by
  obtain ⟨u'⟩ := nonempty_placesOver L' v'
  have : u'.1.asIdeal.LiesOver v.asIdeal := liesOver_trans_of_liesOver v v' u'.1
  have hu : (below L u'.1).asIdeal.LiesOver v.asIdeal :=
    (below_eq_iff _ v).1 (by rw [below_below, (below_eq_iff u'.1 v).2 inferInstance])
  let u : PlacesOver L v := ⟨below L u'.1, hu⟩
  have : u'.1.asIdeal.LiesOver u.1.asIdeal := liesOver_below (K := L) u'.1
  have : IsScalarTower (v.adicCompletion K) (v'.adicCompletion K') (u'.1.adicCompletion L') :=
    .of_algebraMap_eq fun r ↦ (completionMap_completionMap v v' u'.1 r).symm
  have := isMulCommutative_gal_adicCompletion L' v' u'
  have := isMulCommutative_gal_adicCompletion L v u
  let j : u.1.adicCompletion L →ₐ[v.adicCompletion K] u'.1.adicCompletion L' :=
    { completionMap u.1 u'.1 with
      commutes' := fun r ↦ completionMap_completionMap v u.1 u'.1 r }
  have hj : ∀ m : L, j (algebraMap L (u.1.adicCompletion L) m) =
      algebraMap L' (u'.1.adicCompletion L') (algebraMap L L' m) := fun m ↦ by
    change completionMap u.1 u'.1 _ = _
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply L L' (u'.1.adicCompletion L')]
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
  apply (algebraMap L' (u'.1.adicCompletion L')).injective
  rw [algebraMap_localSymbol_apply L' v' u', ← hj, ← hj, algebraMap_localSymbol_apply L v u,
    normResidueSymbol_norm j]

end

end GroundTheory.Global
