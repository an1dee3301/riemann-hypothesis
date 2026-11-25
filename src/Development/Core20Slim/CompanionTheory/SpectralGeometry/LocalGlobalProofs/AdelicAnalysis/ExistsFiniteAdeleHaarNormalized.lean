module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleHaar

theorem exists_haar_integral_one : ∀ (F : Type) [Field F] [NumberField F],
    ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧
      lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _
  have : BorelSpace (Af F) := ⟨rfl⟩
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F :
        Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  refine ⟨Measure.addHaarMeasure (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F),
    inferInstance, ?_⟩
  rw [hset]
  exact Measure.addHaarMeasure_self

end GlobalTheory.CompanionTheory.AdeleHaar
