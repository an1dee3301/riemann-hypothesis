module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor

@[expose] public section

open MvPolynomial Matrix Finset

noncomputable section

namespace GlobalTheory.MinorNorm

section Capelli

variable {R : Type} [CommRing R] [Algebra ℂ R]






variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)






variable {x d}








end Capelli

section Weight

variable {R : Type} [CommRing R] [Algebra ℂ R] {k : ℕ} {x : Fin k → Fin k → R}
  {d : Fin k → Fin k → Derivation ℂ R R}


end Weight

section Fock

variable {σ : Type}













end Fock

section Partition

open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors

variable {l : ℕ}











variable {σ : Type} (v : Fin l → Fin l → σ)





variable {v}





end Partition

end GlobalTheory.MinorNorm
