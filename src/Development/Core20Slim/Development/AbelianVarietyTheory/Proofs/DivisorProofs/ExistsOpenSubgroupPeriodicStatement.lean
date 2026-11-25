module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroup_periodic : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type} (L : ι → AddSubgroup X), (∀ i, IsOpen (L i : Set X)) → (∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) → ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  first | exact @GlobalTheory.WeilM.SB.exists_periodic | exact GlobalTheory.WeilM.SB.exists_periodic | (intros; apply GlobalTheory.WeilM.SB.exists_periodic <;> assumption)
