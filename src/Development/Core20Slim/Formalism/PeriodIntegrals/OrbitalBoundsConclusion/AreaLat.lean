module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.LatDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.AreaLat
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo

@[expose] public section

theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
