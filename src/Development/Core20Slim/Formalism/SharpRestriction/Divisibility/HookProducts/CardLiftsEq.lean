module

public import Development.Core20Slim.Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth
public import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
public import Formalism.SharpRestriction.GrowthBounds.JointsLit
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral
public import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.Row4

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}



theorem card_lifts_eq (D : D7) : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by
  simp [SizeData₂.lifts]









end Formalism.MainNotions.DIV.HookProducts.Row4

end
