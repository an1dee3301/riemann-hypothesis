module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AbsTprod

theorem multipliable_of_summable_abs_sub_one {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) : Multipliable a := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hm := multipliable_one_add_of_summable h'
  have hfun : (fun v => 1 + (a v - 1)) = a := funext fun v => by ring
  rwa [hfun] at hm

theorem tprod_nonneg_of_nonneg {ι : Type} {a : ι → ℝ} (hm : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v := by
  exact tprod_nonneg h0

theorem tprod_ne_zero_of_summable {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (h0 : ∀ v, a v ≠ 0) : ∏' v, a v ≠ 0 := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hne : ∀ v, 1 + (a v - 1) ≠ 0 := fun v => by simpa using h0 v
  have hp := tprod_one_add_ne_zero_of_summable (f := fun v => a v - 1) hne h'
  simpa using hp

theorem tprod_eq_prod_mul_tprod_compl {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (S : Finset ι) :
    Multipliable (fun v : {v // v ∉ S} => a v.1) ∧
      ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1 := by
  have hsub : ∀ p : ι → Prop, Multipliable (fun v : {v // p v} => a v.1) := fun p =>
    GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one (a := fun v : {v // p v} => a v.1)
      (h.comp_injective Subtype.val_injective)
  refine ⟨hsub _, ?_⟩
  have key := Multipliable.tprod_mul_tprod_compl (f := a) (s := (S : Set ι))
    (hsub (· ∈ (S : Set ι))) (hsub (· ∈ (S : Set ι)ᶜ))
  rw [← key, Finset.tprod_subtype']
  rfl

theorem abs_tprod : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  intro ι a h
  have hm := GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one h
  refine ⟨hm, fun S => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl h S, fun hpos => ?_,
    fun h0 => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm h0⟩
  exact lt_of_le_of_ne (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm fun v => (hpos v).le)
    (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable h fun v => (hpos v).ne').symm

end GlobalTheory.CompanionTheory.SW.AbsTprod
