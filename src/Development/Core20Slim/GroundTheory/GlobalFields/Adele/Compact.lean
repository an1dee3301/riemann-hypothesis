module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalAtPlace
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Discrete
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end GroundTheory.Global
