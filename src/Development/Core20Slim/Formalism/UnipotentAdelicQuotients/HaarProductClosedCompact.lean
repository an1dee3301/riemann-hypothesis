module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.D

def haarProductClosedCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ →
    μ ≠ 0 → ∀ P K : Subgroup G, IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ μP μK : Measure G, μP (P : Set G)ᶜ = 0 → (∀ p ∈ P, μP.map (fun x => p * x) = μP) →
      (∀ s : Set G, IsCompact s → μP s ≠ ⊤) → μP ≠ 0 →
      μK Set.univ = 1 → μK (K : Set G)ᶜ = 0 → (∀ k ∈ K, μK.map (fun x => k * x) = μK) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ Φ : G → ℝ≥0∞, Measurable Φ →
        ∫⁻ x, Φ x ∂μ = c * ∫⁻ p, (∫⁻ k, Φ (p * k) ∂μK) ∂μP

end Formalism.D

end
