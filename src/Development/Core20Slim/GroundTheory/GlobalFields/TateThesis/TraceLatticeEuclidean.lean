module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TraceDualLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclidean K).symm.toLinearMap








end

end GroundTheory.Global
