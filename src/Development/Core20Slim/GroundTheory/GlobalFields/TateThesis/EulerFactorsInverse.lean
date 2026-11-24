module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite

@[expose] public section

open NumberField InfinitePlace InfinitePlace.Completion Complex
open scoped Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]






namespace HeckeCharacter

variable (χ : HeckeCharacter K)










end HeckeCharacter

end

end GroundTheory.Global
