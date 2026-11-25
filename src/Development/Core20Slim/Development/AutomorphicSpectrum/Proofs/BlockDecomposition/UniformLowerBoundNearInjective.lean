module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.RealCoordinates

theorem eventually_lower_bound_of_tendsto_injective
    (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ)
    (e : X ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm) (c : P)
    (A : P → X →+ X) (hA : ∀ s, Continuous (A s))
    (hlim : ∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x)))
    (hinj : Function.Injective (A c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  classical

  let f : P → (Fin N → ℝ) →+ (Fin N → ℝ) := fun s =>
    e.toAddMonoidHom.comp ((A s).comp e.symm.toAddMonoidHom)
  have hf : ∀ s, Continuous (f s) := fun s => he.comp ((hA s).comp hes)
  let L : P → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := fun s => (f s).toRealLinearMap (hf s)
  have hL : ∀ s x, e (A s x) = L s (e x) := by
    intro s x
    simp [L, f]
  have hLc : Function.Injective (L c) := by
    intro y z h
    have h' : A c (e.symm y) = A c (e.symm z) := by
      apply e.injective
      simpa [L, f] using h
    simpa using congrArg e (hinj h')

  obtain ⟨K, hK, hKL⟩ := (L c : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hLc)
  have hKpos : (0 : ℝ) < K := hK
  set δ : ℝ := 1 / (2 * K) with hδ
  have hδpos : 0 < δ := by positivity
  have hlow : ∀ y, 2 * δ * ‖y‖ ≤ ‖L c y‖ := by
    intro y
    have h1 := hKL.le_mul_dist y 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
    have h2 : 2 * δ = (K : ℝ)⁻¹ := by
      rw [hδ]
      field_simp
    rw [h2, inv_mul_le_iff₀ hKpos]
    exact h1

  let b : Fin N → Fin N → ℝ := fun i j => if i = j then 1 else 0
  set ε : ℝ := δ / (N + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hev : ∀ᶠ s in nhds c, ∀ i : Fin N, ‖L s (b i) - L c (b i)‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have ht : Filter.Tendsto (fun s => L s (b i)) (nhds c) (nhds (L c (b i))) := by
      have := (he.tendsto _).comp (hlim (e.symm (b i)))
      simpa [L, f, Function.comp_def] using this
    exact (Metric.tendsto_nhds.mp ht ε hεpos).mono fun s hs => by rwa [dist_eq_norm] at hs
  have hNε : (N : ℝ) * ε ≤ δ := by
    rw [hε, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨δ, hδpos, hev.mono fun s hs x => ?_⟩
  rw [hL]
  have hdiff : ‖L s (e x) - L c (e x)‖ ≤ δ * ‖e x‖ := by
    have hy : L s (e x) - L c (e x) = ∑ i, (e x) i • (L s (b i) - L c (b i)) := by
      conv_lhs => rw [pi_eq_sum_univ (e x)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
      rfl
    rw [hy]
    calc ‖∑ i, (e x) i • (L s (b i) - L c (b i))‖
        ≤ ∑ i, ‖(e x) i • (L s (b i) - L c (b i))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, ‖e x‖ * ε := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm (e x) i) (hs i).le (norm_nonneg _) (norm_nonneg _)
      _ = (N : ℝ) * ε * ‖e x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ δ * ‖e x‖ := mul_le_mul_of_nonneg_right hNε (norm_nonneg _)
  have hc := hlow (e x)
  have htri : ‖L c (e x)‖ ≤ ‖L s (e x)‖ + ‖L s (e x) - L c (e x)‖ := by
    calc ‖L c (e x)‖ = ‖L s (e x) - (L s (e x) - L c (e x))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖L s (e x)‖ + ‖L s (e x) - L c (e x)‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (e x)]

end GlobalTheory.CompanionTheory.RealCoordinates
