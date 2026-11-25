module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.HeadOfSiegel
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelDeg
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula

@[expose] public section

theorem PositivityTheory.Rg.Wsf.weilSiegelFormula : GlobalTheory.Published.WeilSiegelFormula :=
  PositivityTheory.PfWsf.Top.head_of_deg GlobalTheory.CompanionTheory.WeilSiegel.Deg.siegelDeg
