module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliableStatement
public import Batteries.Logic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailConst

theorem tail_eq_mul_tail_insert {ι : Type} [DecidableEq ι] (a : ι → ℝ)
    (hs : Summable (fun v => |a v - 1|)) (S : Finset ι) (v : ι) (hv : v ∉ S) :
    ∏' w : {w // w ∉ S}, a w.1 = a v * ∏' w : {w // w ∉ insert v S}, a w.1 := by
  have h := (GlobalTheory.T.infinite_product_multipliable {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.1 {⟨v, hv⟩}
  rw [h.2, Finset.prod_singleton]
  congr 1
  let e : {w : {w // w ∉ S} // w ∉ ({⟨v, hv⟩} : Finset {w // w ∉ S})} ≃
      {w // w ∉ insert v S} :=
    { toFun := fun x => ⟨x.1.1, by
        have h1 := x.1.2
        have h2 := x.2
        simp only [Finset.mem_singleton] at h2
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h3 => h2 (Subtype.ext h3), h1⟩⟩
      invFun := fun y => ⟨⟨y.1, fun h3 => y.2 (Finset.mem_insert_of_mem h3)⟩, by
        simp only [Finset.mem_singleton]
        intro h3
        exact y.2 (by
          have := congrArg Subtype.val h3
          simp only at this
          simp [this])⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  exact e.tprod_eq (fun w => a w.1)

theorem tail_pos {ι : Type} (a : ι → ℝ) (hs : Summable (fun v => |a v - 1|)) (S : Finset ι)
    (hpos : ∀ v, v ∉ S → 0 < a v) : 0 < ∏' w : {w // w ∉ S}, a w.1 :=
  (GlobalTheory.T.infinite_product_multipliable {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.2.1 (fun w => hpos w.1 w.2)

theorem exists_const_mul_tail : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by
  intro ι _ a c S₁ _ hs hc
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 / 2 :=
    hs.tendsto_cofinite_zero.eventually (Iio_mem_nhds (by norm_num))
  have hfin : {v | ¬ |a v - 1| < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  let S₀ : Finset ι := S₁ ∪ hfin.toFinset
  have hS₀ : ∀ v, v ∉ S₀ → 0 < a v := by
    intro v hv
    have h1 : |a v - 1| < 1 / 2 := by
      by_contra h2
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h2))
    have h2 := (abs_lt.1 h1).1
    linarith
  have hposS : ∀ S, S₀ ⊆ S → 0 < ∏' v : {v // v ∉ S}, a v.1 := fun S hS =>
    tail_pos a hs S (fun v hv => hS₀ v (fun h => hv (hS h)))
  have hP₀ := hposS S₀ (Finset.Subset.refl _)
  refine ⟨⟨(c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1, div_nonneg (c S₀).2 hP₀.le⟩, S₀,
    Finset.subset_union_left, fun S hS => ⟨hposS S hS, ?_⟩⟩
  have key : ∀ T : Finset ι, (c (S₀ ∪ T) : ℝ) =
      ((c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1) * ∏' v : {v // v ∉ S₀ ∪ T}, a v.1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.union_empty]
      field_simp
    | insert v T _ ih =>
      by_cases hv : v ∈ S₀ ∪ T
      · have h1 : S₀ ∪ insert v T = S₀ ∪ T := by
          rw [Finset.union_insert, Finset.insert_eq_of_mem hv]
        rw [h1]
        exact ih
      · have h1 : S₀ ∪ insert v T = insert v (S₀ ∪ T) := Finset.union_insert _ _ _
        have hsub : S₀ ⊆ S₀ ∪ T := Finset.subset_union_left
        have hav : 0 < a v := hS₀ v (fun h => hv (hsub h))
        have h2 := hc (S₀ ∪ T) (Finset.Subset.trans Finset.subset_union_left hsub) v hv
        have h3 := tail_eq_mul_tail_insert a hs (S₀ ∪ T) v hv
        rw [h1]
        rw [h2, h3] at ih
        have h4 : (c (insert v (S₀ ∪ T)) : ℝ) * a v = (((c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1) * ∏' w : {w // w ∉ insert v (S₀ ∪ T)}, a w.1) * a v := by
          rw [ih]; ring
        exact mul_right_cancel₀ hav.ne' h4
  have h := key S
  rw [Finset.union_eq_right.2 hS] at h
  exact h

end GlobalTheory.CompanionTheory.SW.TailConst
