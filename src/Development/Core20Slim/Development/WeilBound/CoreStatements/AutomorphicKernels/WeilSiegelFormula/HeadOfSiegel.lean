module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.EcHeisSch
public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisCells
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.SiegelND
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonHermMain
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEisensteinSiegelConvergence
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSiegelFormulaOfChaptersLI
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependent
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellOfPoissonSiegel
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSecondTermFromParts
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSiegelParabolicInvariance
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvariance
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishing
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PullSchLI
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

namespace PositivityTheory.PfWsf.Top

theorem pull : PositivityTheory.GramSchwartzFunctions.PullSchLI := GlobalTheory.CompanionTheory.PullSch.pullSchLI
theorem orb : PositivityTheory.GramSchwartzFunctions.ThetaOrbits := GlobalTheory.CompanionTheory.ThetaOrbit.thetaOrbits

theorem head_of_two (hE : PositivityTheory.GramSchwartzFunctions.EisCells) (hB : PositivityTheory.GramSchwartzFunctions.BigCell) : GlobalTheory.Published.WeilSiegelFormula :=
  GlobalTheory.CompanionTheory.SiegelAssemblyLI.weilSiegelFormula_of_chapters_LI
    (GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary)
    GlobalTheory.WeilEisConv.weilEisensteinSiegelConvergence pull hE orb hB

theorem big_of_three (h1 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h2 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h3 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) :
    PositivityTheory.GramSchwartzFunctions.BigCell :=
  GlobalTheory.CompanionTheory.WeilSiegel.bigCell_of_poisson_siegel GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH h1 GlobalTheory.CompanionTheory.SplitGram.hasSum_IfrB h2 h3

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_three (h4 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND)
    (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_two GlobalTheory.CompanionTheory.EisCellsChapter.eisCells (big_of_three h4 h5 h6)
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_siegel (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_three GlobalTheory.CompanionTheory.HermPoisson.poissonHerm_main h5 h6
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_deg (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_siegel PositivityTheory.PfWsf.Hand.Merge.siegelND h6
end PositivityTheory.PfWsf.Top
