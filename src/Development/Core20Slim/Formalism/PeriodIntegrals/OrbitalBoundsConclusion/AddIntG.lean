module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.AddIntGTop

@[expose] public section

theorem additive_integral_generation : PI.AddIntG.Target := PI.AddIntG.Wk.addIntG_top
