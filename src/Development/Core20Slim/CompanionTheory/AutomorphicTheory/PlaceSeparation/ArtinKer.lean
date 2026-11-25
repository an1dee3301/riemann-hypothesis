module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.Conductor
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ConductorIdeal
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Pi
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace CompanionTheory.FamInh

theorem isOpen_connInf (E : Type) [Field E] [NumberField E] :
    IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) :
      Set (InfiniteAdeleRing E)ˣ) := by
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  have he : IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := he.locallyConnectedSpace
  exact isOpen_connectedComponent

theorem ofInfinite_eq_map (E : Type) [Field E] [NumberField E] (y : (InfiniteAdeleRing E)ˣ) :
    (ofInfinite y : IdeleGroup E) =
      Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) y :=
  Units.ext rfl

theorem comap_connectedComponent (E : Type) [Field E] [NumberField E] :
    (Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)).comap (GroundTheory.Global.IdeleClassGroup.mk E) =
      ((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E).topologicalClosure := by
  apply le_antisymm
  · intro x hx
    have hx' : IdeleClassGroup.mk E x ∈ connectedComponent (1 : IdeleClassGroup E) := hx
    show x ∈ closure (((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E : Subgroup (IdeleGroup E)) :
      Set (IdeleGroup E))
    rw [mem_closure_iff_nhds]
    intro t ht
    have hc : Continuous fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => x * (ofFinite u : IdeleGroup E)⁻¹ :=
      continuous_const.mul continuous_ofFinite.inv
    have hW : (fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => x * (ofFinite u : IdeleGroup E)⁻¹) ⁻¹' t ∈ 𝓝 1 :=
      hc.continuousAt.preimage_mem_nhds (by simpa using ht)
    obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hW
    have hsupp : (Function.support n).Finite :=
      S.finite_toSet.subset fun v hv => by
        by_contra h
        exact hv (hn0 v h)
    let V : Subgroup (IdeleGroup E) :=
      (Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ).comap (toInfinite E) ⊓
        (finiteLevel n).comap (toFinite E)
    have hV : IsOpen (V : Set (IdeleGroup E)) :=
      ((isOpen_connInf E).preimage (continuous_toInfinite E)).inter
        ((isOpen_finiteLevel hsupp).preimage (continuous_toFinite E))
    have hVo : IsOpen ((V.map (IdeleClassGroup.mk E) : Subgroup (IdeleClassGroup E)) : Set (IdeleClassGroup E)) :=
      IdeleClassGroup.isOpenMap_mk E _ hV
    have hcl : IsClopen ((V.map (IdeleClassGroup.mk E) : Subgroup (IdeleClassGroup E)) : Set (IdeleClassGroup E)) :=
      ⟨Subgroup.isClosed_of_isOpen _ hVo, hVo⟩
    obtain ⟨y, hy, hyx⟩ := hcl.connectedComponent_subset (one_mem _) hx'
    have hk : x * y⁻¹ ∈ (IdeleClassGroup.mk E).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
    rw [IdeleClassGroup.ker_mk] at hk
    refine ⟨x * (ofFinite (toFinite E y))⁻¹, hsub hy.2, ?_⟩
    have e : x * (ofFinite (toFinite E y))⁻¹ = (x * y⁻¹) * ofInfinite (toInfinite E y) := by
      have h := ofFinite_mul_ofInfinite y
      generalize ofFinite (toFinite E y) = a at h ⊢
      generalize ofInfinite (toInfinite E y) = b at h ⊢
      subst h
      rw [mul_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact Subgroup.mul_mem_sup hk ⟨toInfinite E y, hy.1, (ofInfinite_eq_map E _).symm⟩
  · refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
    · rintro _ ⟨k, rfl⟩
      show IdeleClassGroup.mk E (diagonal E k) ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup E)
      rw [IdeleClassGroup.mk_diagonal]
      exact one_mem _
    · rintro _ ⟨y, hy, rfl⟩
      let f : (InfiniteAdeleRing E)ˣ →* IdeleClassGroup E := (IdeleClassGroup.mk E).comp
        (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))
      have hf : Continuous f := (IdeleClassGroup.continuous_mk E).comp
        (Continuous.units_map _ (continuous_id.prodMk continuous_const))
      have h := hf.image_connectedComponent_subset 1 ⟨y, hy, rfl⟩
      rw [map_one] at h
      exact h
    · exact isClosed_connectedComponent.preimage (IdeleClassGroup.continuous_mk E)

end CompanionTheory.FamInh

end
