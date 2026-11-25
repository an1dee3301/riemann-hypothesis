module

public import Mathlib

@[expose] public section

noncomputable section

open Matrix

namespace Formalism.IndefR.DeterminantProjection

section Ring

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]




end Ring

section Herm

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]













end Herm

section Field

variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]


end Field

end Formalism.IndefR.DeterminantProjection

end
