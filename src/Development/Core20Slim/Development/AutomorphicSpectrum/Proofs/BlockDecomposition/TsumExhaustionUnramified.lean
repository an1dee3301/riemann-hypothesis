module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory.CompanionTheory.Exhaustion

open Filter Topology

variable {α E : Type*} [NormedAddCommGroup E]

theorem exists_subset_of_exhaustion {C : ℕ → Finset α} (hC : Monotone C) (hex : ∀ a, ∃ k, a ∈ C k)
    (s : Finset α) : ∃ k, s ⊆ C k :=
  ((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists

theorem summable_norm_of_exhaustion {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable fun a => ‖f a‖ := by
  refine summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_
  obtain ⟨k, hk⟩ := exists_subset_of_exhaustion hC hex s
  exact (Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)

theorem tsum_exhaust [CompleteSpace E] {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable f ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a)) := by
  have hs : Summable f := (summable_norm_of_exhaustion hC hex hK).of_norm
  exact ⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩

theorem tsum_exhaust_prop : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  intro α f C hC hex ⟨K, hK⟩
  exact ⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩

end GlobalTheory.CompanionTheory.Exhaustion
