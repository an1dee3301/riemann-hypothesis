module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology

namespace GlobalTheory

open Filter Topology in
private theorem norm_update_sub_update_sub_smul_le {k : ℕ} (F : (Fin k → ℝ) → ℂ)
    (d : Fin k → (Fin k → ℝ) → ℂ)
    (hF : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (i : Fin k) (t y : Fin k → ℝ) {ε δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ z, dist z t < δ → ‖d i z - d i t‖ ≤ ε) (hy : dist y t < δ) {a b : ℝ}
    (ha : dist a (t i) < δ) (hb : dist b (t i) < δ) :
    ‖F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t‖ ≤ ε * |b - a| := by
  set g : ℝ → ℂ := fun s => F (Function.update y i s) - s • d i t with hg
  have hmem : ∀ s ∈ Metric.ball (t i) δ, dist (Function.update y i s) t < δ := by
    intro s hs
    rw [dist_pi_lt_iff hδ]
    intro m
    by_cases hm : m = i
    · subst hm
      simpa using hs
    · rw [Function.update_of_ne hm]
      exact lt_of_le_of_lt (dist_le_pi_dist y t m) hy
  have hderiv : ∀ s ∈ Metric.ball (t i) δ,
      HasDerivWithinAt g (d i (Function.update y i s) - d i t) (Metric.ball (t i) δ) s := by
    intro s _
    have h1 := hF i (Function.update y i s)
    simp only [Function.update_idem, Function.update_self] at h1
    have h2 : HasDerivAt (fun u : ℝ => u • d i t) ((1 : ℝ) • d i t) s :=
      (hasDerivAt_id s).smul_const (d i t)
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Metric.ball (t i) δ, ‖d i (Function.update y i s) - d i t‖ ≤ ε :=
    fun s hs => hgood _ (hmem s hs)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_ball (t i) δ) (Metric.mem_ball.2 ha) (Metric.mem_ball.2 hb)
  have hdiff : g b - g a = F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t := by
    simp only [hg, sub_smul]
    abel
  rw [hdiff, Real.norm_eq_abs] at key
  exact key


open Filter Topology in
theorem _root_.GlobalTheory.hasFDerivAt_of_continuous_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k F d hF hd t
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (k + 1) with hε
  have hεpos : 0 < ε := div_pos hc (by positivity)
  have hev : ∀ᶠ z in 𝓝 t, ∀ i, dist (d i z) (d i t) < ε :=
    eventually_all.2 fun i => (hd i).continuousAt.eventually (Metric.ball_mem_nhds (d i t) hεpos)
  obtain ⟨δ, hδ, hδgood⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ i z, dist z t < δ → ‖d i z - d i t‖ ≤ ε := fun i z hz =>
    (dist_eq_norm (d i z) (d i t) ▸ (hδgood hz i)).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  set p : ℕ → (Fin k → ℝ) := fun j m => if (m : ℕ) < j then t m + h m else t m with hp
  set a : ℕ → ℂ := fun j => if hj : j < k then h ⟨j, hj⟩ • d ⟨j, hj⟩ t else 0 with ha
  have hp0 : p 0 = t := by
    funext m
    simp [hp]
  have hpk : p k = t + h := by
    funext m
    simp [hp, m.isLt]
  have hsumL : (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h =
      ∑ j ∈ Finset.range k, a j := by
    rw [Finset.sum_range]
    simp [ha, ContinuousLinearMap.sum_apply]
  have htel : F (t + h) - F t = ∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j)) := by
    rw [Finset.sum_range_sub (fun j => F (p j)) k, hpk, hp0]
  have hpdist : ∀ j, dist (p j) t < δ := by
    intro j
    rw [dist_pi_lt_iff hδ]
    intro m
    simp only [hp]
    split_ifs
    · rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h m) hh
    · simpa using hδ
  have hstep : ∀ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ ≤ ε * ‖h‖ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set i : Fin k := ⟨j, hjk⟩ with hi
    have haj : a j = ((t i + h i) - t i) • d i t := by
      simp [ha, hjk, hi]
    have hnext : p (j + 1) = Function.update (p j) i (t i + h i) := by
      funext m
      by_cases hm : m = i
      · subst hm
        simp [hp, hi]
      · have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext e)
        rw [Function.update_of_ne hm]
        simp only [hp]
        have : (m : ℕ) < j + 1 ↔ (m : ℕ) < j := by omega
        simp only [this]
    have hcur : p j = Function.update (p j) i (t i) := by
      symm
      rw [Function.update_eq_self_iff]
      simp [hp, hi]
    have hx : dist (t i + h i) (t i) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h i) hh
    have hmain := norm_update_sub_update_sub_smul_le F d hF i t (p j) hδ (hgood i) (hpdist j)
      (a := t i) (b := t i + h i) (by rw [dist_self]; exact hδ) hx
    rw [haj, hnext]
    conv_lhs => rw [hcur]
    rw [Function.update_idem]
    refine hmain.trans ?_
    gcongr
    rw [add_sub_cancel_left]
    simpa using norm_le_pi_norm h i
  calc ‖F (t + h) - F t - (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h‖
      = ‖∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j) - a j)‖ := by
        rw [hsumL, htel, ← Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ε * ‖h‖ := Finset.sum_le_sum hstep
    _ = k * (ε * ‖h‖) := by simp
    _ ≤ c * ‖h‖ := by
        rw [← mul_assoc]
        gcongr
        rw [hε, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end GlobalTheory
