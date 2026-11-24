module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

def SemidirectCovering.Statement (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] : Prop :=
  ∀ (i : L →* H) (q : H →* L) (j : N →* H), Continuous i → Continuous q → IsClosedEmbedding j →
    (∀ l, q (i l) = l) → (∀ g, q g = 1 ↔ g ∈ j.range) →
    ∀ (μL : Measure L) [μL.IsHaarMeasure] (μN : Measure N) [μN.IsHaarMeasure],
    (∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j) →
    ∀ (Γ : Subgroup H) (C : Set N) (T : Set L), IsCompact C → MeasurableSet T → μL T < ⊤ →
      (∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C) → (∀ l, ∃ γ ∈ Γ, q γ * l ∈ T) →
      ∀ (ν : Measure H) [ν.IsHaarMeasure],
        ∃ S : Set H, MeasurableSet S ∧ ν S < ⊤ ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ S

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
