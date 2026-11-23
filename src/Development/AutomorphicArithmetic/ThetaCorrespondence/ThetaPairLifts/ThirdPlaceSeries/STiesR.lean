module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting
namespace Formalism.L2.SG.SpectralTiesReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
structure STiesRAlt (R : RecTAlt ex) extends STies D where
  tr : ∀ u, ColDict.Transport X u ((R.T.cols.forms u).to0)
  into : ∀ u, ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = InstExistsPf.instOf D
  G : RowDict.GoodOp X
  rowTie : ∀ hF : FinX Y, RowDict.RowDictTie X G (hI hF).eHH
  locTied : Pf.LocCP.LocTied D
end Formalism.L2.SG.SpectralTiesReal
end
end
