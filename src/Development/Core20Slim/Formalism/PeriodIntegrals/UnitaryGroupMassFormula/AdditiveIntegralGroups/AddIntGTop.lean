module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG

@[expose] public section

namespace PI.AddIntG.Wk

theorem addIntG_top : PI.AddIntG.Target := glue_holds_var formalGroupLawExists

end PI.AddIntG.Wk
