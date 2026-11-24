module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TraceSum
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem traceSum_holds : TraceSum := sumEqTrace_holds

theorem trace_sum_over_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.TraceMapNormalisation D := trace_sum_over_letters traceSum_holds D

end Formalism.MainNotions.Ext
