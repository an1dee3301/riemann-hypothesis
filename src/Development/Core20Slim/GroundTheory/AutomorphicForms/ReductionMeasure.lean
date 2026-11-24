module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionMahler
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Restrict
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  have := GroundTheory.Global.countable_numberField K
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      SecondCountableTopology ↥(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun v =>
    inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
  have hemb := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))
  set O : Set (FiniteAdeleRing (𝓞 K) K) :=
    Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite) with hO
  have hOsc : SecondCountableTopology O :=
    hemb.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hOopen : IsOpen O := hemb.isOpen_range
  have hOmem : ∀ x : FiniteAdeleRing (𝓞 K) K, x ∈ O ↔
      x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := fun x => by
    constructor
    · rintro ⟨y, rfl⟩ v
      exact (y v).2
    · intro h
      exact ⟨fun v => ⟨x v, h v⟩, rfl⟩
  let U : K → Set (FiniteAdeleRing (𝓞 K) K) := fun k => (· - algebraMap K _ k) ⁻¹' O
  have hU : ∀ k, SecondCountableTopology (U k) := fun k => by
    have he : IsEmbedding (Set.codRestrict
        ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)) ∘
          (Subtype.val : U k → FiniteAdeleRing (𝓞 K) K)) O fun x => x.2) :=
      ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)).isEmbedding.comp
        IsEmbedding.subtypeVal).codRestrict _ _
    exact he.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
    (fun k => hOopen.preimage (continuous_sub_right _)) ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles x
    exact ⟨k, (hOmem _).2 hk⟩

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance secondCountableTopology_matrix {R : Type*} [TopologicalSpace R] [SecondCountableTopology R]
    {n : ℕ} : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))

instance measurableSpace_adelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.AdelicGL K n) := borel _

instance borelSpace_adelicGL {n : ℕ} : BorelSpace (AdelicGLn.AdelicGL K n) := ⟨rfl⟩

instance measurableSpace_finiteAdelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.FiniteAdelicGL K n) :=
  borel _

instance borelSpace_finiteAdelicGL {n : ℕ} : BorelSpace (AdelicGLn.FiniteAdelicGL K n) := ⟨rfl⟩

instance measurableSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    MeasurableSpace (GL (Fin n) w.Completion) :=
  borel _

instance borelSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    BorelSpace (GL (Fin n) w.Completion) := ⟨rfl⟩



end Reduction

end

end GroundTheory.Automorphic
