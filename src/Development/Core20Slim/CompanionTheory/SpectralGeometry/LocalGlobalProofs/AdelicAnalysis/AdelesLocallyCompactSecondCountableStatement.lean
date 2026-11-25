module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeles_locally_compact_second_countable : ∀ (F : Type) [Field F] [NumberField F], (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧ (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  first | exact @GlobalTheory.CompanionTheory.AdeleTop.adele_top | exact GlobalTheory.CompanionTheory.AdeleTop.adele_top | (intros; apply GlobalTheory.CompanionTheory.AdeleTop.adele_top <;> assumption)
