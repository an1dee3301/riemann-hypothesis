module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.SgOneOfParts
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JMapVal
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jtop
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jcpt
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemStabLine
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKGL
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapScalarVal
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TriangularLowerRightDiag
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHtHalfSub
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsParComap
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapHalfTr
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Brat
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleMapMemIntAdIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionEmbeddingAlgebraMapOfTotallyReal
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.BlgOfDict
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinIdele
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseCM
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

@[expose] public section

namespace PositivityTheory.RgEis.So

theorem sgOne_hd : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := fun sl _ sc sg dict _ cg gt bl el pl mg =>
  have jt := GlobalTheory.CompanionTheory.EisSo.jtop
  have jc := GlobalTheory.CompanionTheory.RgEisSo.jcpt sg gt jt
  have ji := GlobalTheory.CompanionTheory.RgEisSo.JIwaAd.jiwa sg
  have jch := GlobalTheory.CompanionTheory.EisSo.jCh sg bl jt
  sgOne_of_parts
    (GlobalTheory.CompanionTheory.SgOneBase.baseCM cg GlobalTheory.CompanionTheory.RgEisFix.bFix GlobalTheory.CompanionTheory.EisBrat.brat GlobalTheory.CompanionTheory.RgEisBInt.bInt GlobalTheory.CompanionTheory.RgEisSo.bInf (GlobalTheory.CompanionTheory.RgEisSo.Hd.blg_of_dict dict) GlobalTheory.CompanionTheory.CMDelta.bDel)
    GlobalTheory.CompanionTheory.RgEis.Cover.jEx jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat (GlobalTheory.CompanionTheory.EisSec.jSec_of_top jt) jch
    (GlobalTheory.CompanionTheory.EisJMir.jmir sg gt bl el pl jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat jch) (GlobalTheory.CompanionTheory.RgDescendWall.descend2 sl) (GlobalTheory.CompanionTheory.RgEisTwist.twist sl) sc cg gt pl mg

end PositivityTheory.RgEis.So
