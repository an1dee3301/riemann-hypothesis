module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem cA_mem_idAt {P : Pl D → Prop} {a : AE D} (h : a ∈ idAt D P) : cA D a ∈ idAt D P := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (localComponents D P).1
  rw [hε] at h ⊢
  conv_rhs => rw [← h]
  rw [map_mul, hc]












end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}









end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}



end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}


end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}


end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}



end GlobalTheory.LastOpPf
