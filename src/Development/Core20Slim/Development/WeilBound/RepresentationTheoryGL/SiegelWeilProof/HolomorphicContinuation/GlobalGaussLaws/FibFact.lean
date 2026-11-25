module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Sw.Glob.Fib

variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X]
  [BorelSpace X]

theorem fib_meas (μ : Measure X) [μ.IsAddRightInvariant] (π : X →+ (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) →+ X) (hπs : ∀ u, π (s u) = u) (g : X → ℝ≥0∞) (hg : Measurable g)
    (hgs : ∀ z u, g (z + s u) = g z)
    (hloc : ∀ K : Set (Fin m → Fin n → ℂ), IsCompact K → ∫⁻ z, K.indicator 1 (π z) * g z ∂μ ≠ ∞) :
    ∃ c : ℝ≥0, (μ.withDensity g).map π = c • (volume : Measure (Fin m → Fin n → ℂ)) := by
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity g).map π with hν
  have hπm : Measurable π := hπ.measurable
  have hint : ∀ a : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable a → ∫⁻ u, a u ∂ν = ∫⁻ z, a (π z) * g z ∂μ := by
    intro a ha
    rw [hν, lintegral_map ha hπm]
    have e := lintegral_withDensity_eq_lintegral_mul μ hg (ha.comp hπm)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  have hinv : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hint _ (measurable_one.indicator (measurable_const_add u hA)),
      hint _ (measurable_one.indicator hA)]
    have key : ∀ z, ((fun x => u + x) ⁻¹' A).indicator 1 (π z) * g z =
        (fun z => A.indicator 1 (π z) * g z) (z + s u) := by
      intro z
      simp only [map_add (f := _), hπs, hgs]
      congr 1
      by_cases h : u + π z ∈ A
      · simp [Set.indicator, h, add_comm]
      · simp [Set.indicator, h, add_comm]
    simp_rw [key]
    exact lintegral_add_right_eq_self (fun z => A.indicator 1 (π z) * g z) (s u)
  have hfc : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [← lintegral_indicator_one hK.measurableSet, hint _ (measurable_one.indicator hK.measurableSet)]
    exact (hloc K hK).lt_top
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact ⟨Measure.addHaarScalarFactor ν volume, Measure.isAddLeftInvariant_eq_smul ν volume⟩

end PositivityTheory.Rg.Sw.Glob.Fib
