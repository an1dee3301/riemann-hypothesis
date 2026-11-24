module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

namespace GlobalTheory.TwistedCosetSum

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem coset_integral [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X)
    [μ.IsAddLeftInvariant] (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (g : X → ℂ)
    (hg : ∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) (c : X) :
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = 0 ∨
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = g c * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  set S : Set X := (fun x => -c + x) ⁻¹' (U : Set X) with hS
  have hmem : ∀ y, y ∈ S ↔ -c + y ∈ U := fun y => Iff.rfl
  have hmeas : MeasurableSet S := (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : μ S = μ U := measure_preimage_add μ _ _
  by_cases h : ∀ u ∈ U, g (c + u) = g c
  · right
    have : S.indicator g = S.indicator (fun _ => g c) := by
      refine Set.indicator_congr fun y hy => ?_
      have := h _ ((hmem y).1 hy)
      rwa [add_neg_cancel_left] at this
    rw [this, integral_indicator_const _ hmeas]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · left
    push_neg at h
    obtain ⟨u, hu, hne⟩ := h
    have hc0 : g c ≠ 0 := by
      intro h0
      have := hg c u hu u hu
      rw [h0, mul_zero] at this
      exact hne (by rw [h0]; exact mul_self_eq_zero.1 this.symm)
    have hshift : ∀ y, S.indicator g (u + y) * g c = g (c + u) * S.indicator g y := by
      intro y
      have hiff : u + y ∈ S ↔ y ∈ S := by
        rw [hmem, hmem, add_left_comm]
        exact U.add_mem_cancel_left hu
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.2 hy)]
        have := hg c u hu _ ((hmem y).1 hy)
        rw [add_neg_cancel_left, show c + u + (-c + y) = u + y by abel] at this
        exact this
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hiff.1 h)), zero_mul, mul_zero]
    have h1 : (∫ y, S.indicator g y ∂μ) * g c = g (c + u) * ∫ y, S.indicator g y ∂μ := by
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (S.indicator g) u]
      rw [← integral_mul_const, ← integral_const_mul]
      simp only [hshift]
    have h2 : (g (c + u) - g c) * ∫ y, S.indicator g y ∂μ = 0 := by
      rw [sub_mul, ← h1]; ring
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

theorem integral_eq_sum_twisted : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  intro X _ _ _ _ _ _ μ _ U hU _ g hc hg
  classical
  by_cases hint : Integrable g μ
  swap
  · exact ⟨∅, by rw [integral_undef hint]; simp⟩
  haveI := GlobalTheory.LCIntegralField.discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        g y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y).2 h)]
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hsum : ∫ y, g y ∂μ = ∑ c ∈ T, ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ := by
    rw [← integral_finsetSum _ fun c _ => hint.indicator (hmeas c)]
    exact congrArg _ hdec
  refine ⟨(T.filter fun c => ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ ≠ 0).image
    Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h), hsum, ← Finset.sum_filter_ne_zero,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact (coset_integral μ U hU g hg (Quotient.out c)).resolve_left (Finset.mem_filter.1 hc).2

end GlobalTheory.TwistedCosetSum
