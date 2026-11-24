module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLin
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS

@[expose] public section

namespace Formalism.IndefR.Fin

theorem splitLinF (D : Formalism.BasicNotions.D7) : SplitLin D := splitLin_of (placeLatDual D) (latLevelF D)

end Formalism.IndefR.Fin
