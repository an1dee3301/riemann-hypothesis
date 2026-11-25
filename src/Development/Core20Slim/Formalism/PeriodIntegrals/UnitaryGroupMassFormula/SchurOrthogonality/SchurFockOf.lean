module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.Assembly
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionA
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionB
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionC
public import Formalism.PeriodIntegrals.HwIrred
public import Development.Core20Slim.Formalism.PeriodIntegrals.SchurFock

@[expose] public section

noncomputable section

namespace PI.WSF

theorem schurFock_of (h : PI.HwIrred) : PI.SchurFock :=
  schurFock_of_steps unitary_haar_measure (schurOrth_of h evaluation_at_one)

end PI.WSF
