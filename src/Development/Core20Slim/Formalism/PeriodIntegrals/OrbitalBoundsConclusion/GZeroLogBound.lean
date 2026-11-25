module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.GZeroLogBound
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearCardBound.ZeroLogBound

@[expose] public section

theorem GZeroLogBound : PI.GZeroLogBound.Target := PI.GZeroLogBound.UnitaryGroupMassFormula.target
