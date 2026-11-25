module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.LatDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.AreaLat
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem discrNe_holds : DiscrNe := discrNe'

theorem sigmaStarEx_holds : SigmaStarEx := sigma_star_exists

end Formalism.MainNotions.Ext
