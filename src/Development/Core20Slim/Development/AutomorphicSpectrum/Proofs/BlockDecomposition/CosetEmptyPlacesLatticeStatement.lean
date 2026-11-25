module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLattice
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_empty_places_lattice : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (I : Ideal (𝓞 F)) (x0 : ι → F), cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | exact GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | (intros; apply GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset <;> assumption)
