module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CFinal
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGood
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Assemble
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Gunr


theorem unrWhit : PositivityTheory.SiegelWeilFormula.Gen.UnrWhit := unrWhit_of_parts locC almostGood

end PositivityTheory.SiegelWeilFormula.Gunr
