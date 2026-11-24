module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

@[expose] public section

theorem UpperTheory.Reformulated.B.MultiDimensional.multi_dim :
    ∀ {P : Type} [inst : Fintype P] (g : P → ℤ → ENNReal), ∑' (x : P → ℤ), ∏ p : P, g p (x p) ≤ ∏ p : P, ∑' (n : ℤ), g p n := by
  intro P _ g
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ x ∈ s, ∏ p : P, g p (x p)
      ≤ ∑ x ∈ Fintype.piFinset (fun p => s.image (fun y : P → ℤ => y p)), ∏ p : P, g p (x p) := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        exact Fintype.mem_piFinset.2 fun p => Finset.mem_image_of_mem _ hx
    _ = ∏ p : P, ∑ n ∈ s.image (fun y : P → ℤ => y p), g p n :=
        (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ p : P, ∑' (n : ℤ), g p n :=
        Finset.prod_le_prod' fun p _ => ENNReal.sum_le_tsum _
