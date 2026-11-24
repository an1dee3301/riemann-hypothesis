module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.BeConjNorm
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.BeConjNormOfIntInv
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.MemIntegerRingIffNormLeOne

@[expose] public section

theorem conjugate_norm_bound : PI.BeConjNorm.BeConjNorm :=
  PI.BeConjNormW.beConjNorm_of_intInv PI.BeConjNormW.inverse_integral_padic
