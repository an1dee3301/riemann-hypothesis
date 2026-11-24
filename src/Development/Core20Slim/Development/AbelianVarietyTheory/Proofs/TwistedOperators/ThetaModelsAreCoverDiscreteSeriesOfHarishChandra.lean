module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

namespace GlobalTheory.CoverModel

theorem modelsAreCoverSeries_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  modelsAreCoverSeries

end GlobalTheory.CoverModel
