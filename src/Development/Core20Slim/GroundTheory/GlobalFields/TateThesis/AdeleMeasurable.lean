module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Bases
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K]

instance secondCountableTopology_infinitePlaceCompletion (w : InfinitePlace K) :
    SecondCountableTopology w.Completion :=
  (Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

noncomputable instance measurableSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    MeasurableSpace w.Completion :=
  borel _

instance borelSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    BorelSpace w.Completion :=
  ⟨rfl⟩

variable [NumberField K]

instance secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology (∀ w : InfinitePlace K, w.Completion))

noncomputable instance measurableSpace_infiniteAdeleRing : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ w : InfinitePlace K, w.Completion))

instance borelSpace_infiniteAdeleRing : BorelSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (BorelSpace (∀ w : InfinitePlace K, w.Completion))

noncomputable instance measurableSpace_finiteAdeleRing :
    MeasurableSpace (FiniteAdeleRing (𝓞 K) K) :=
  borel _

instance borelSpace_finiteAdeleRing : BorelSpace (FiniteAdeleRing (𝓞 K) K) :=
  ⟨rfl⟩

noncomputable instance measurableSpace_adeleRing : MeasurableSpace 𝔸[K] :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance borelSpace_adeleRing : BorelSpace 𝔸[K] :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Global
