module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

instance secondCountableTopology_units_complex : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

instance borelSpace_units_complex : BorelSpace ℂˣ where
  measurable_eq := by
    rw [congrArg (@borel ℂˣ) Units.isOpenEmbedding_val.isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := ℂ)]
    rfl

def UnitsInvHaar.Statement (I : Type*) [Fintype I] : Prop :=
  ∀ (ρ : Measure (I → ℂˣ)) [ρ.IsHaarMeasure], ∃ c : ℝ≥0, c ≠ 0 ∧
    ∀ (k : ℕ) (g : (I → ℂˣ) → ℝ≥0∞) (g' : (I → ℂ) → ℝ≥0∞), Measurable g →
      (∀ (b : I → ℂ) (hb : ∀ i, b i ≠ 0), g' b = g fun i => (Units.mk0 (b i) (hb i))⁻¹) →
      ∫⁻ a, (∏ i, ‖(a i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g a ∂ρ =
        c * ∫⁻ b, (∏ i, ‖b i‖ₑ ^ (2 * k)) * g' b

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
