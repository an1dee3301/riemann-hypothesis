module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
public import Init.Classical
public import Init.Core
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailCut

theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a) := by
    intro T
    have hs : Summable fun v => ‖T.mulIndicator a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum
      by_cases hv : v ∈ T
      · simp [Set.mulIndicator_of_mem hv, Real.norm_eq_abs]
      · simp [Set.mulIndicator_of_notMem hv]
    have h := multipliable_one_add_of_summable hs
    simpa using h
  have e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have hsplit : (∏' v, Set.mulIndicator {v | v ∉ S} a v) =
      ∏' v, (Set.mulIndicator (↑(S' \ S) : Set ι) a v * Set.mulIndicator {v | v ∉ S'} a v) := by
    refine tprod_congr fun v => ?_
    by_cases h1 : v ∈ S
    · have h2 : v ∈ S' := hSS' h1
      simp [Set.mulIndicator, h1, h2]
    · by_cases h2 : v ∈ S'
      · simp [Set.mulIndicator, h1, h2]
      · simp [Set.mulIndicator, h1, h2]
  have hfin : (∏' v, Set.mulIndicator (↑(S' \ S) : Set ι) a v) = ∏ v ∈ S' \ S, a v := by
    rw [tprod_eq_prod (s := S' \ S)]
    · exact Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv) a
    · intro v hv
      exact Set.mulIndicator_of_notMem (by rwa [Finset.mem_coe]) a
  rw [e1, e2, hsplit, Multipliable.tprod_mul (hmul _) (hmul _), hfin]

end GlobalTheory.CompanionTheory.SW.TailCut
