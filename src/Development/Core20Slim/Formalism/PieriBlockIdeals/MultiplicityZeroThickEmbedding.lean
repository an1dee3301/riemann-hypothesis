module

public import Development.Core20Slim.Formalism.PieriBlockIdeals.MertensReciprocalElementary

@[expose] public section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent



structure Labels (ι : Type) (N : ℕ) where
  cc : ι → ι
  Φ : Set ι
  U : ι → Fin N → ℤ
  U' : ι → Fin N → ℤ
  bot : ι → ℤ

namespace Labels

variable {ι : Type} {N : ℕ}





end Labels






end Formalism.CohomologicalDescent.WorkedExample
