module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.DYhc7.Iwa :
    {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → Prop :=
    fun {G : Type} [Group G] (P K : Subgroup G) ↦ ∀ (g : G), ∃ p ∈ P, ∃ k ∈ K, g = p * k

theorem UpperTheory.Reformulated.B.DYhc7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {K P : Subgroup G},
      IsCompact (↑K : Set G) →
        IsClosed (↑P : Set G) →
          UpperTheory.Reformulated.B.DYhc7.Iwa P K → Topology.IsQuotientMap fun (x : ↥P × ↥K) ↦ (↑x.1 : G) * (↑x.2 : G) := by
  intro G _ _ _ K P hK hP hI
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let h : G × K ≃ₜ G × K :=
    { toFun := fun y => (y.1 * (y.2 : G), y.2)
      invFun := fun y => (y.1 * (y.2 : G)⁻¹, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : P → G) (id : K → K)) :=
    hP.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  have hcl : IsClosedMap (fun x : ↥P × ↥K ↦ (x.1 : G) * (x.2 : G)) := by
    have h1 : IsClosedMap (Prod.fst : G × K → G) := isClosedMap_fst_of_compactSpace
    exact h1.comp (h.isClosedMap.comp hι.isClosedMap)
  refine hcl.isQuotientMap (by fun_prop) ?_
  intro g
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
