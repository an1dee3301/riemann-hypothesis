module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupport
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_of_projection_support : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  first | exact @GlobalTheory.FiberPointwise.vanish_at_point | exact GlobalTheory.FiberPointwise.vanish_at_point | (intros; apply GlobalTheory.FiberPointwise.vanish_at_point <;> assumption)
