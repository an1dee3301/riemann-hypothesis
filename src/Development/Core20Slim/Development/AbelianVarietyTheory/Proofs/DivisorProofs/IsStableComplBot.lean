module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.DefTransfer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}





variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

variable {θ M}

end GlobalTheory.DefTransfer

end
