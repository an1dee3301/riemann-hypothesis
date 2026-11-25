module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponentStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order

@[expose] public section

noncomputable section

namespace GlobalTheory.LocVec

open scoped BigOperators

section Algebra

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]



end Algebra

section Topology

theorem finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) {C : Set G} (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) (H : Subgroup K)
    (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  classical
  open scoped Pointwise in
  obtain ⟨W, hWo, hWH⟩ := isOpen_induced_iff.1 hH
  have h1 : (1 : G) ∈ W := by
    have : (1 : K) ∈ (H : Set K) := H.one_mem
    rw [← hWH] at this
    exact this
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  have hV' : V⁻¹ ∈ nhds (1 : G) := inv_mem_nhds_one G hV
  have hint : (interior V⁻¹).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hV'⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC hint
  have key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton := by
    rintro g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    apply QuotientGroup.eq.2
    have hk1 : (g * (k : G))⁻¹ ∈ V := hk
    have hk2 : (g * (k' : G))⁻¹ ∈ V := hk'
    have := hVW _ hk1 _ hk2
    have hmem : ((k⁻¹ * k' : K) : G) ∈ W := by
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]
      group
    have : (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W := hmem
    rw [hWH] at this
    exact this
  have hfin : (Set.univ : Set (K ⧸ H)).Finite := by
    refine (t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by
      simpa using ht (hKC k.2)
    exact Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩
  haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end GlobalTheory.LocVec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocVec


end GlobalTheory.LocVec
