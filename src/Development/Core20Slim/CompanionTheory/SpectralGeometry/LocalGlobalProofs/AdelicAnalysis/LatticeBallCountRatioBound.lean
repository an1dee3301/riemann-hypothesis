module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.Packing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖

theorem Sep.card_le {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)

theorem exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩

theorem Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega

end GlobalTheory.CompanionTheory.Adelic.Packing


open GlobalTheory.CompanionTheory.Adelic.Packing in
theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
