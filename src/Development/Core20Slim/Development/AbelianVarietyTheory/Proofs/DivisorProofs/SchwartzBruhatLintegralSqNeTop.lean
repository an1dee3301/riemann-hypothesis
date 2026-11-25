module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.SBNorm

theorem schwartzBruhat_memL2_inner_self : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  intro k _ _ _ _ n d μ hμ f hf
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hfc : Continuous f := hf.1.continuous
  have hint : ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
    intro g hg
    have hgc : Continuous g := hg.1.continuous
    exact (hfc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport
      (hf.2.mul_right (f' := fun y => (starRingEnd ℂ) (g y)))
  have hpt : ∀ y, ‖f y * (starRingEnd ℂ) (f y)‖ₑ = ‖f y‖ₑ ^ 2 := by
    intro y
    rw [enorm_mul, pow_two]
    congr 1
    simp [enorm_eq_nnnorm]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (hint f hf).2
    unfold HasFiniteIntegral at this
    simp_rw [hpt] at this
    exact this.ne
  refine ⟨hfin, ?_, ?_, hint⟩
  · have h1 : ∀ y, f y * (starRingEnd ℂ) (f y) = (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
      intro y
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖f y‖ ^ 2)
      (Filter.Eventually.of_forall fun y => by positivity)
      ((hfc.norm.pow 2).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · intro hne
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmeas : Measurable fun y => ‖f y‖ₑ ^ 2 := (hfc.measurable.enorm).pow_const 2
    rw [← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]
    have hsupp : Function.support (fun y => ‖f y‖ₑ ^ 2) = f ⁻¹' {0}ᶜ := by
      ext y
      simp
    rw [hsupp]
    exact (hf.1 ({0}ᶜ)).measure_pos μ ⟨x, hx⟩

end GlobalTheory.SBNorm
