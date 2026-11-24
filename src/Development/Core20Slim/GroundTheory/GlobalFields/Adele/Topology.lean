module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalAtPlace
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.Restricted
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

variable (K : Type*) [Field K] [NumberField K]

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩

instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (.of_forall fun v ↦ isCompact_adicCompletionIntegers v)

theorem t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstance

instance locallyCompactSpace_adeleRing : LocallyCompactSpace 𝔸[K] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem t2Space_adeleRing : T2Space 𝔸[K] :=
  inferInstance

instance IdeleGroup.locallyCompactSpace : LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

instance locallyCompactSpace_units_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K)ˣ :=
  inferInstance

instance locallyCompactSpace_units_infiniteAdeleRing :
    LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  inferInstance

end GroundTheory.Global
