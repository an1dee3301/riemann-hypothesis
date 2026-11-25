module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedMemOfOrbitHeight
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Order.SupIndep

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_mem_of_orbit_height_separation : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  first | exact @GlobalTheory.fixed_mem_of_orbit_height | exact GlobalTheory.fixed_mem_of_orbit_height | (intros; apply GlobalTheory.fixed_mem_of_orbit_height <;> assumption)
