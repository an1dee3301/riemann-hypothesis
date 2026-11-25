module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ProperActionOrbitMeasure
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_action_orbit_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V), (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) → (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z → (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) → ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 → ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 → ∃ c : ℝ≥0, μ = c • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | exact GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | (intros; apply GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique <;> assumption)
