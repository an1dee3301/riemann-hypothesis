module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Order

@[expose] public section

open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem countable_quotient_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Countable (G ⧸ W) := by
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW
  have h : IsLindelof (Set.univ : Set (G ⧸ W)) := by
    rw [← Set.image_univ_of_surjective (QuotientGroup.mk_surjective (s := W))]
    exact isLindelof_univ.image QuotientGroup.continuous_mk
  exact Set.countable_univ_iff.1 h.countable_of_discrete

variable {K}



end

end GroundTheory.Global
