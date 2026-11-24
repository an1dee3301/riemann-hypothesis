module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrabilityStatement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := GlobalTheory.T.fockVectors_overVacuum_isometry

end GlobalTheory
