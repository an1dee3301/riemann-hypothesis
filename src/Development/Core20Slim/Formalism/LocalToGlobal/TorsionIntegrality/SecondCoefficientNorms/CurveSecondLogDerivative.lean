module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CurveIntegerMultiplicationSeries
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll

@[expose] public section

namespace Formalism.L2.Th1.C

theorem curveFrame : CurveFrame := curve_formal_frame
theorem curve_second_log_derivative : CurveSecondLogDerivative := curve_second_log_derivative_holds
theorem curveEndoR : CurveEndoR := curve_real_multiplication_series

end Formalism.L2.Th1.C
