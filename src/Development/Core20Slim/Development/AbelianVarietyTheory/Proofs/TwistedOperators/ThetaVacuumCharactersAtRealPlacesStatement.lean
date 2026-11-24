module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlaces
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_atRealPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  first | exact @GlobalTheory.vacChar_of_record | exact GlobalTheory.vacChar_of_record | (intros; apply GlobalTheory.vacChar_of_record <;> assumption)
