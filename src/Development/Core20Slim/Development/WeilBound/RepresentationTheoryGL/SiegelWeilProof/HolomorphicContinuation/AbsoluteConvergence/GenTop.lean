module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IEqOfSL
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGen
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRight
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOpOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BasisM
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec

@[expose] public section

namespace PositivityTheory.Rg.Sw.AbsSt


theorem absThm_of' (hV : VacOut) (hI : Iwa) (hD : CayleyBlocksInvertible) (hK : KAK) (hM : Mult) (hS : SecZero) (hDF : DerivativeVacuumDilations)
    (hC : CycSec) (_hSph : Sph) (hH : HolParam) (hG : Glue) (hLC : LC) (_hN : NullIff) : AbsThm :=
  absThm_gen hV (Proj.projOp hI hM) (tsGen hI hD hK hM hS hDF hH hLC) (basis hI hD hM hC hH) (farRight hI hD hM hH)
    hS hLC hH hG

end PositivityTheory.Rg.Sw.AbsSt
