module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace UpperTheory.Reformulated.B.Yva3.Helpers

private lemma key {α ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) (u : Finset (ι → α)) :
    ∑ ξ ∈ u, ∏ i, f (ξ i) ≤ ∏ _i : ι, ∑' x, f x := by
  have h1 : ∑ ξ ∈ u, ∏ i, f (ξ i)
      ≤ ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ξ hξ
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hξ
    · intro ξ _ _
      exact Finset.prod_nonneg fun i _ => h0 (ξ i)
  have h2 : ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i)
      = ∏ i, ∑ x ∈ u.image (fun η => η i), f x :=
    by rw [Finset.prod_univ_sum]
  have h3 : ∏ i, ∑ x ∈ u.image (fun η => η i), f x ≤ ∏ _i : ι, ∑' x, f x := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg fun x _ => h0 x
    · intro i _
      exact hf.sum_le_tsum _ (fun x _ => h0 x)
  exact h1.trans (h2.le.trans h3)

private lemma summ {α ι : Type} [Fintype ι] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) : Summable fun (ξ : ι → α) ↦ ∏ i : ι, f (ξ i) := by
  classical
  exact summable_of_sum_le (fun ξ => Finset.prod_nonneg fun i _ => h0 (ξ i)) (key hf h0)

end UpperTheory.Reformulated.B.Yva3.Helpers

theorem UpperTheory.Reformulated.B.Yva3.main :
    ∀ {k : Type} [inst : Field k] [NumberField k] {ι : Type} [inst : Fintype ι] {f : k → ℝ},
      Summable f → (∀ (a : k), (0 : ℝ) ≤ f a) → Summable fun (ξ : ι → k) ↦ ∏ i : ι, f (ξ i) := by
  intro k _ _ ι _ f hf h0
  exact UpperTheory.Reformulated.B.Yva3.Helpers.summ hf h0
