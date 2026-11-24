module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open scoped TensorProduct

namespace GlobalTheory.St.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


def embA (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) : VA X.B.I :=
  ∑ j, ιA.symm (x j) • qA X wt j



end GlobalTheory.St.G

end
