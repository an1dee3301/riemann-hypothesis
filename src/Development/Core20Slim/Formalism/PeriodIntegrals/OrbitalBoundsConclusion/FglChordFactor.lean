module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglChordFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.FormalGroupChordFactor

@[expose] public section

theorem fglChordFactor : PI.FglChordFactor.Lemma := PI.FglChordFactor.Wk.formal_group_chord_factor
