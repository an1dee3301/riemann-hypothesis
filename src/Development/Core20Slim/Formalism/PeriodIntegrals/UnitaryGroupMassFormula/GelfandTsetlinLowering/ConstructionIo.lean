module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoXiHw
public import Formalism.PeriodIntegrals.HwIrred
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioExists_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of' h3 h4 hx

end PI.WGL
