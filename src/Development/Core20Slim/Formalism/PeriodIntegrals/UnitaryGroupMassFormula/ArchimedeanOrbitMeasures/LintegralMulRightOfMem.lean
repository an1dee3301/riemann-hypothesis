module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.UniformEmbedding

@[expose] public section

noncomputable section

namespace PI.AprimeInfA

open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  let _ := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]









variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]





end Abstract

end PI.AprimeInfA
