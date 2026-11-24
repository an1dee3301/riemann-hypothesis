module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityAbelianizationRestrictReciprocityLimi
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.NormGroups
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Notation.Bracket
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced

@[expose] public section

namespace GroundTheory.LocalField.Abstract

section TopologicalAbelianization

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

theorem topologicalClosure_commutator_le_comap (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap f := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

def topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)


end TopologicalAbelianization

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem continuous_inclusion {K K' : Subgroup G} (hK : K' ≤ K) :
    Continuous (Subgroup.inclusion hK) :=
  continuous_subtype_val.subtype_mk _

def limitRestrict {K K' : OpenSubgroup G} (hK : K' ≤ K) :
    TopologicalAbelianization (K' : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) :=
  topologicalAbelianizationMap (Subgroup.inclusion hK) (continuous_inclusion hK)

@[simp]
theorem limitRestrict_mk {K K' : OpenSubgroup G} (hK : K' ≤ K) (g : (K' : Subgroup G)) :
    limitRestrict hK (g : TopologicalAbelianization (K' : Subgroup G)) =
      ((⟨g, hK g.2⟩ : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem limitRestrict_reciprocityLimit {K K' : OpenSubgroup G} (hK : K' ≤ K)
    (a : fixedModule A (K' : Subgroup G)) :
    limitRestrict hK (D.reciprocityLimit hax K' a) =
      D.reciprocityLimit hax K (norm A (K : Subgroup G) (K' : Subgroup G) a) := by
  refine D.eq_reciprocityLimit hax fun L hL _ => ?_
  have hmap : (commutator (K' : Subgroup G)).map (Subgroup.inclusion hK) ≤
      commutator (K : Subgroup G) := by
    rw [commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hL' : IsAbelianExtension K' (L ⊓ K') := by
    refine ⟨inf_le_right, fun x hx => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have h1 := hL.commutator_le (hmap ⟨x, hx, rfl⟩)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have := hL'.normal
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K' a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL' a
  rw [← hg, abelianizationRestrict_mk] at e
  rw [← hg, limitRestrict_mk, abelianizationRestrict_mk]
  have h := D.reciprocity_galRestrict hax hL.le hL'.le hK inf_le_left
    (g : (K' : Subgroup G) ⧸ ((L ⊓ K' : OpenSubgroup G) : Subgroup G).subgroupOf K')
  rw [galRestrict_mk, e, normTateZero_mk] at h
  exact h

end ClassFieldData

end GroundTheory.LocalField.Abstract
