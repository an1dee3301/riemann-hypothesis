module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleTop

theorem t2Space_finiteAdeleRing_of_numberField (F : Type) [Field F] [NumberField F] : T2Space (Af F) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

theorem t2Space_infiniteAdeleRing_of_numberField_field (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem adele_top : ∀ (F : Type) [Field F] [NumberField F],
    (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧
    (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  intro F _ _
  refine ⟨⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_adele F, ?_⟩,
    GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, t2Space_finiteAdeleRing_of_numberField F⟩
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.CompanionTheory.AdeleTop
