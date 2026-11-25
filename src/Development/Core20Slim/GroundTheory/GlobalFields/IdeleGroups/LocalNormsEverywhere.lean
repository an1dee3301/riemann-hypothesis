module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.Splitting
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Valuation.ValuationSubring

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]


attribute [local instance] FractionRing.liftAlgebra in
variable (K L) in
theorem eventually_ramificationIdx_eq_one :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [eventually_cofinite]
  refine (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun w hw ↦ ?_
  by_contra h
  have := w.isPrime
  have := not_dvd_differentIdeal_iff.1 h
  exact hw (Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 K))

theorem map_integerUnitsOver_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : PlacesOver L v) (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) =
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  classical
  refine le_antisymm (map_integerUnitsOver_le v) fun u hu ↦ ?_
  obtain ⟨y, hy, hyu⟩ := exists_norm_eq_of_ramificationIdx_eq_one v w.1 he hu
  refine ⟨Pi.mulSingle w y, mem_integerUnitsOver.2 fun w' ↦ ?_, ?_⟩
  · by_cases h : w' = w
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hy
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  · rw [finiteLocalNorm_mulSingle]
    exact Units.ext hyu


variable (L) in
theorem eventually_map_integerUnitsOver_eq :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      (integerUnitsOver L v).map (finiteLocalNorm L v) =
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  refine (eventually_forall_placesOver K (eventually_ramificationIdx_eq_one K L)).mono
    fun v hv ↦ ?_
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hv w)


variable (L) in
theorem mem_range_ideleNorm_iff_forall (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range := by
  rw [mem_range_ideleNorm_iff]
  refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  filter_upwards [eventually_finiteProj_mem (L := K) x, eventually_map_integerUnitsOver_eq L]
    with v hv hv'
  rw [hv']
  exact hv

theorem mem_range_ideleNorm_of_forall (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) :
    x ∈ (ideleNorm K L).range :=
  (mem_range_ideleNorm_iff_forall L x).2 ⟨hfin, hinf⟩

end IdeleNorm

end

end GroundTheory.Global
