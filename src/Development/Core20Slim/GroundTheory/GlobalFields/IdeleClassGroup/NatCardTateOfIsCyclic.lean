module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import Development.Core20Slim.GroundTheory.GlobalFields.SecondInequality.Cyclic
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandCyclic
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.Invariants
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.CompleteTrivial
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Subtype.Order
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.OpenSubgroup

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem natCard_tate_of_isCyclic (K L : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) [(L.subgroupOf K).Normal]
    [(L.subgroupOf K).FiniteIndex] {F E : FiniteSubfield} (hFE : F ≤ E)
    (hK : K = F.1.fixingSubgroup) (hL : L = E.1.fixingSubgroup)
    (hcyc : IsCyclic (K ⧸ L.subgroupOf K)) :
    Nat.card (tateZero IdeleClassLimit K L) = L.relIndex K ∧
      Nat.card (tateNegOne IdeleClassLimit K L) = 1 := by
  subst hK hL
  have : Fact (F ≤ E) := ⟨hFE⟩
  have : IsGalois F.1 E.1 := isGalois_of_normal (F := F) (E := E)

  have hcycE : IsCyclic (E.1 ≃ₐ[F.1] E.1) := by
    let φ := QuotientGroup.lift (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup)
      (restrictHom (F := F) (E := E)) (ker_restrictHom (F := F) (E := E)).ge
    refine isCyclic_of_surjective φ fun x ↦ ?_
    obtain ⟨g, rfl⟩ := restrictHom_surjective (F := F) (E := E) x
    exact ⟨g, rfl⟩
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E.1 ≃ₐ[F.1] E.1)
  have hax := classFieldAxiom_ideleClassGroup (K := F.1) (L := E.1) σ hσ
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (tateZeroEquivGalois (F := F) (E := E)).toEquiv,
      GroundTheory.LocalField.natCard_tateZero_eq hσ, hax.1]
    exact (relIndex_fixingSubgroup hFE).symm
  · rw [Nat.card_congr (tateNegOneEquivGalois (F := F) (E := E)).toEquiv,
      GroundTheory.LocalField.natCard_tateNegOne_eq hσ, hax.2]

theorem classFieldAxiom : ClassFieldAxiom (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (V : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (ofOpenSubgroup_le hVU) (fixingSubgroup_ofOpenSubgroup U).symm
    (fixingSubgroup_ofOpenSubgroup V).symm hcyc

end IdeleClassLimit

end

end GroundTheory.Global
