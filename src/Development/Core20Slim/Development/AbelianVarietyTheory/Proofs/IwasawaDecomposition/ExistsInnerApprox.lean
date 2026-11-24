module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem Std.exists_inner_approx {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) :
    ∃ (m : ℕ) (S : Fin m → List (Mx n)), (∀ i, ∀ X ∈ S i, X ∈ lieSet ε) ∧ ∀ δ : ℝ, 0 < δ → ∃ u : H,
      ∀ z, Sm ε σ z → ‖ℓ z - ⟪u, z⟫_ℂ‖ ≤ δ * ∑ i, ‖Dw σ (S i) z‖ := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  refine ⟨m, S, hS, fun δ hδ => ?_⟩
  have hx : ∀ i, ∃ x ∈ smooth (Jm ε) σ, dist ((InnerProductSpace.toDual ℂ H).symm (Λ i)) x < δ := fun i =>
    Metric.mem_closure_iff.1 (h.dense_smooth _) δ hδ
  choose x hxs hxd using hx
  choose u hu using fun i => exists_adjoint (isUnit_Jm ε) h.1 (S i) (hS i) (x i) (hxs i)
  refine ⟨∑ i, u i, fun z hz => ?_⟩
  rw [hΛ z hz, sum_inner, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← hu i z hz, ← InnerProductSpace.toDual_symm_apply, ← inner_sub_left]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [← dist_eq_norm]
  exact (hxd i).le

theorem avgBd_sobCont : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (T : H → H) (Z : Set (Mx n)) (C : ℝ), IsCompact Z →
    Z ⊆ UJset ε → 0 ≤ C → AvgBd σ T Z C → ∀ (ι : Type) [Fintype ι] (ℓ : ι → (H →ₗ[ℂ] ℂ)) (w : ι → H),
    (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (w j)) → (∀ j, Sm ε σ (T (w j))) → ∀ M : ℝ, 0 ≤ M →
    (∀ y ∈ Z, ‖∑ j, ℓ j (σ y (w j))‖ ≤ M) → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M := by
  intro n ε H _ _ _ σ h T Z C hZ hZU hC hA ι _ ℓ w hℓ hw hTw M hM hb
  choose m S hS hap using fun j => h.exists_inner_approx (hℓ j)
  have hc : ContinuousOn (fun y => ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖) Z :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
      ((h.continuousOn_Dw (hS j i) (hw j)).mono hZU).norm
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn hc
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖ ≤ K := fun y hy =>
    ((le_abs_self _).trans (hK₀ y hy)).trans (le_max_left _ _)
  set K' := ∑ j, ∑ i, ‖Dw σ (S j i) (T (w j))‖ with hK'
  have key : ∀ δ : ℝ, 0 < δ → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M + δ * (C * K + K') := by
    intro δ hδ
    choose u hu using fun j => hap j δ hδ
    have hd : ∀ z : ι → H, (∀ j, Sm ε σ (z j)) →
        ‖∑ j, ℓ j (z j) - ∑ j, ⟪u j, z j⟫_ℂ‖ ≤ δ * ∑ j, ∑ i, ‖Dw σ (S j i) (z j)‖ := fun z hz => by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hu j _ (hz j))
    have h1 := hA ι u w (M + δ * K) (by positivity) fun y hy => by
      have e1 := hd (fun j => σ y (w j)) fun j => (hw j).translate h.1 (hZU hy)
      have e2 := norm_le_norm_add_norm_sub (∑ j, ℓ j (σ y (w j))) (∑ j, ⟪u j, σ y (w j)⟫_ℂ)
      have e3 := mul_le_mul_of_nonneg_left (hK y hy) hδ.le
      have e4 := hb y hy
      linarith
    have h2 := hd (fun j => T (w j)) hTw
    have h3 := norm_le_norm_add_norm_sub' (∑ j, ℓ j (T (w j))) (∑ j, ⟪u j, T (w j)⟫_ℂ)
    nlinarith
  have ht : Tendsto (fun δ : ℝ => C * M + δ * (C * K + K')) (𝓝[>] 0) (𝓝 (C * M + 0 * (C * K + K'))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)

end GlobalTheory.TypeSum

end
