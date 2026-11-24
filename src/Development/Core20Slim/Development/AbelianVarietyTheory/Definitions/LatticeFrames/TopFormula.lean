module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.HermitianForms.TiedSym

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

def HasMat (h : GA D D.sp.X')
    (y : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  h ∈ GfC D.sp.X' ∧ ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j = y.1 (finCongr (rankP D) i) (finCongr (rankP D) j)





end GlobalTheory.Core.Rk.Top

end
