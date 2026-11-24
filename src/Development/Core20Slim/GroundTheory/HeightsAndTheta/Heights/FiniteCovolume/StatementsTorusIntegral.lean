module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

def TorusIntegralHomogeneous.Statement (κ : Type*) [Fintype κ] : Prop :=
  ∀ q : κ → ℝ, (∀ i, 0 < q i) → ∀ n : ℕ, ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ t : ℝ, 0 < t →
    ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
      C * ENNReal.ofReal (t ^ ((2 * n + 2) * Fintype.card κ))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
