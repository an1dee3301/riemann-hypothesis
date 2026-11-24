module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg2
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
public import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}


structure RealPack (ex : Extra D L hT Gi Gl Kc Yd cX) where

  R : Formalism.L2.RecT ex

  S : Formalism.L2.SG.SpectralTiesReal.STiesR R

  P : RowSideFamily ex

  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)

  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)

  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3

  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]

  Q : RealT R P Dcf Spf Zscf S Ks

attribute [instance] RealPack.fKs RealPack.nKs RealPack.aKs

variable {ex : Extra D L hT Gi Gl Kc Yd cX}


abbrev cxW (W : RealPack ex) := W.Q.Rl.toCx3 W.Q.F


end GlobalTheory.MiS

end
