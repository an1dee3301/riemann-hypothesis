module

public import Mathlib
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice

@[expose] public section

noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

















section Pair

variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

end Pair

namespace FlagExample

open NumberField 

variable (E : Type) [Field E] [NumberField E] [StarRing E]

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

end FlagExample

end GlobalTheory.SA

end
