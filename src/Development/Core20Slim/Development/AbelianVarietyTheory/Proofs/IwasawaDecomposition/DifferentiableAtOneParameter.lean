module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory

namespace GlobalTheory.LocWeil.DerComm

theorem _root_.GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter {A : Type} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (φ : ℝ → A) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hm : ∀ s t : ℝ, φ (s + t) = φ s * φ t) : DifferentiableAt ℝ φ 0 := by
  have hφ := hc
  have hadd := hm
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > (0 : ℝ), ∀ s : ℝ, |s| ≤ δ → ‖1 - φ s‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.mp hφ.continuousAt (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hs' : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero]; linarith
    have := h hs'
    rw [dist_eq_norm, h0, norm_sub_rev] at this
    exact this.le
  set E : A := δ⁻¹ • ∫ s in (0 : ℝ)..δ, (1 - φ s) with hE
  have hEn : ‖E‖ < 1 := by
    have hI : ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      apply hball
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [sub_zero, abs_of_pos hδ] at hI
    rw [hE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ δ⁻¹ * (1 / 2 * δ) := by gcongr
      _ < 1 := by field_simp; norm_num
  set G : ℝ → A := fun x => ∫ s in (0 : ℝ)..x, φ s with hG
  have hint : ∀ t : ℝ, φ t * (1 - E) = δ⁻¹ • (G (t + δ) - G t) := by
    intro t
    have hC : 1 - E = δ⁻¹ • ∫ s in (0 : ℝ)..δ, φ s := by
      rw [hE, intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul, inv_mul_cancel₀ hδ.ne',
        one_smul, sub_sub_cancel]
    rw [hC, mul_smul_comm, hG,
      intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)]
    congr 1
    have key := (ContinuousLinearMap.mul ℝ A (φ t)).intervalIntegral_comp_comm
      (hφ.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at key
    rw [← key]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun s => φ s) t]
    simp [add_comm]
  set u : Aˣ := Units.oneSub E hEn with hu
  have hrep : φ = fun t => (δ⁻¹ • (G (t + δ) - G t)) * ↑u⁻¹ := by
    funext t
    rw [← hint t]
    have : (1 - E : A) = ↑u := by rw [hu, Units.val_oneSub]
    rw [this, Units.mul_inv_cancel_right]
  have hGd : ∀ x : ℝ, DifferentiableAt ℝ G x := fun x =>
    (hφ.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  rw [hrep]
  have h1 : DifferentiableAt ℝ (fun t => G (t + δ)) 0 :=
    (hGd (0 + δ)).comp (0 : ℝ) (differentiableAt_id.add_const δ)
  have h2 : DifferentiableAt ℝ (fun t => δ⁻¹ • (G (t + δ) - G t)) 0 :=
    by
      have h3 := (h1.sub (hGd 0)).const_smul δ⁻¹
      exact h3
  exact h2.mul_const _

section Alg

variable {S U : Type} [AddCommGroup S] [Module ℂ S]

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)

variable {β b b'}

variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}

section Main

variable {Γ I : Type} [Group Γ] (ω : Γ →* Module.End ℂ S) (G : Γ →* (U →L[ℝ] U)) (ev : I → S →ₗ[ℂ] ℂ) {f : S}
  {N : Submodule ℂ S}
  (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) (hκ : κ ≠ 0)
  (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
  (hω : ∀ q u, ω q * d u = d (G q u) * ω q) (hG : ∀ q x y, β (G q x) (G q y) = β x y)
  (hN : ∀ Φ, Φ ∈ N ↔ ∃ a ∈ Algebra.adjoin ℂ (Set.range d), a f = Φ)
  (hvac : ∀ B ∈ Algebra.adjoin ℂ (Set.range d), (∀ u, B (d u f) = d u (B f)) → ∃ c : ℂ, B f = c • f)
  (hev : ∀ Φ Ψ, (∀ w, ev w Φ = ev w Ψ) → Φ = Ψ)
  (hline : ∀ w u, ∃ ℓ : ℝ → S →ₗ[ℂ] ℂ, ℓ 0 = ev w ∧ (∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (d u Ψ)) s) ∧
    ∀ s, ∃ (c : ℂ) (w' : I), ∀ Ψ, ℓ s Ψ = c * ev w' Ψ)

end Main

end Alg

end GlobalTheory.LocWeil.DerComm

end
