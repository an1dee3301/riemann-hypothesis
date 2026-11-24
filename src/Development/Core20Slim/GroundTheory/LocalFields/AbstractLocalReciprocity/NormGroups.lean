module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.UniqueQuotientSubgroupOfSelf
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

namespace GroundTheory.LocalField.Abstract

section Abelian

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsAbelianExtension (K L : OpenSubgroup G) : Prop :=
  L ≤ K ∧ commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K

variable {K L : OpenSubgroup G}

theorem IsAbelianExtension.le (h : IsAbelianExtension K L) : L ≤ K :=
  h.1

theorem IsAbelianExtension.commutator_le (h : IsAbelianExtension K L) :
    commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K :=
  h.2

theorem IsAbelianExtension.normal (h : IsAbelianExtension K L) :
    ((L : Subgroup G).subgroupOf K).Normal :=
  Subgroup.Normal.of_commutator_le _ h.2

theorem IsAbelianExtension.isMulCommutative (h : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 h.2

theorem isAbelianExtension_of_isMulCommutative (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] : IsAbelianExtension K L :=
  ⟨hLK, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance⟩


theorem IsAbelianExtension.inf {L' : OpenSubgroup G} (h : IsAbelianExtension K L)
    (h' : IsAbelianExtension K L') : IsAbelianExtension K (L ⊓ L') :=
  ⟨inf_le_left.trans h.le, fun _ hx => ⟨h.2 hx, h'.2 hx⟩⟩

theorem isAbelianExtension_self (K : OpenSubgroup G) : IsAbelianExtension K K :=
  ⟨le_rfl, fun x _ => x.2⟩

variable [IsTopologicalGroup G]






end Abelian

section NormGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Type*) [CommGroup A] [MulDistribMulAction G A]

noncomputable def normGroup (K L : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (norm A (K : Subgroup G) (L : Subgroup G)).range

variable {A}

theorem normGroup_mono {K L H : OpenSubgroup G} (hLH : L ≤ H) (hHK : H ≤ K) :
    normGroup A K L ≤ normGroup A K H :=
  range_norm_le_range_norm hLH hHK

end NormGroup


namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

section Reciprocity

variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem mk_eq_one_iff [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔ (x : G) ∈ (L : Subgroup G) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem exists_reciprocity_mk_eq (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (a : fixedModule A (K : Subgroup G)) :
    ∃ x : (K : Subgroup G),
      D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax
    (a : tateZero A (K : Subgroup G) (L : Subgroup G))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, hq⟩

theorem reciprocity_mk_of_le {L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K : L' ≤ K) [((L' : Subgroup G).subgroupOf K).Normal]
    (hLL' : L ≤ L') (x : (K : Subgroup G)) (a : fixedModule A (K : Subgroup G))
    (h : D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    D.reciprocity hL'K hax (x : (K : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L' : Subgroup G)) := by
  have e := D.reciprocity_galRestrict hax hL'K hLK le_rfl hLL'
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  rw [galRestrict_mk, h, normTateZero_mk, norm_self] at e
  exact e

theorem reciprocity_injective (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] : Function.Injective (D.reciprocity hL.le hax) :=
  haveI := hL.isMulCommutative
  (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax).1

theorem reciprocity_mk_eq_one_iff (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔
      (x : G) ∈ (L : Subgroup G) := by
  rw [← mk_eq_one_iff, ← (D.reciprocity_injective hax hL).eq_iff, map_one]

theorem mem_normGroup_iff_of_reciprocity (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] {x : (K : Subgroup G)}
    {a : fixedModule A (K : Subgroup G)}
    (h : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    a ∈ normGroup A K L ↔ (x : G) ∈ (L : Subgroup G) := by
  rw [← D.reciprocity_mk_eq_one_iff hax hL, h, QuotientGroup.eq_one_iff]
  rfl

end Reciprocity

section Limitation

variable {K L : OpenSubgroup G}

include D hax


end Limitation

section Correspondence

variable {K L L' : OpenSubgroup G}

include D hax

theorem normGroup_le_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L ≤ normGroup A K L' ↔ L ≤ L' := by
  refine ⟨fun h => ?_, fun h => normGroup_mono h hL'.le⟩
  have hI := hL.inf hL'
  have := hI.normal
  have := hL.normal
  have := hL'.normal
  intro g hg
  have hgK : g ∈ (K : Subgroup G) := hL.le hg
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hI.le hax
    ((⟨g, hgK⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ ((L ⊓ L' : OpenSubgroup G) : Subgroup G).subgroupOf K))
  have h1 := D.reciprocity_mk_of_le hax hI.le hL.le inf_le_left ⟨g, hgK⟩ a ha.symm
  have h2 := D.reciprocity_mk_of_le hax hI.le hL'.le inf_le_right ⟨g, hgK⟩ a ha.symm
  exact (D.mem_normGroup_iff_of_reciprocity hax hL' h2).1
    (h ((D.mem_normGroup_iff_of_reciprocity hax hL h1).2 hg))



end Correspondence

end ClassFieldData

end GroundTheory.LocalField.Abstract
