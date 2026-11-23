module

public import Formalism.LocalToGlobal.GaloisLevelStructure.LinkChar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
namespace Formalism.L2
def NGalTiedAlt.TupLink {D : BasicNotions.D7} (G : NGalTiedAlt D) {C : Host.CharFrame D} {nch : BasicNotions.NChoice D}
    (Tp : Host.TupTied D C nch) : Prop :=
  G.tup = Tp.tup
end Formalism.L2
end
