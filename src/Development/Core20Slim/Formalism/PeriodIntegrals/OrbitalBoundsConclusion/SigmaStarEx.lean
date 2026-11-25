module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.LatDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.SigmaStarEx
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx

@[expose] public section

theorem sigma_star_exists : PI.SigmaStarEx := PI.SSE.sigmaStarEx
