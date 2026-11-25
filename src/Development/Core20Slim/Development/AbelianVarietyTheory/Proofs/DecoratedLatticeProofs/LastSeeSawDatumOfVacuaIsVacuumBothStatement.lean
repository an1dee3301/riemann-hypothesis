module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  first | exact @GlobalTheory.LastVacPf.lastVac | exact GlobalTheory.LastVacPf.lastVac | (intros; apply GlobalTheory.LastVacPf.lastVac <;> assumption)
