module

public import Formalism.LocalToGlobal.ClassRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPinMin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GTiedFOfC2S

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure RecTAlt (ex : Extra D L hT Gi Gl K Y cX) where
  T : TiedDataSKAlt ex
  pin : Rows.RowPinMinAlt T
  joints : JointsSAlt T.toTiedDataS
  host : HostDatumSelfDual T.toTiedDataS
  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W
def ExtraDataRecursive (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (RecTAlt ex)
theorem ExtraDataRecursive.tiedSK {ex : Extra D L hT Gi Gl K Y cX} (h : ExtraDataRecursive ex) : ExtraDataSelfDualKernel ex :=
  let ⟨R⟩ := h; ⟨R.T⟩
end
def SecondLayerFamilyClass : FamClass := fun {_} Fm =>
  (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ExtraDataRecursive (Fm.ex x hx i)) ∧ LinkedFamiliesAligned' Fm
theorem SecondLayerFamilyClass.c2sk {eps : ℝ} {Fm : FamP eps} (h : SecondLayerFamilyClass Fm) : LinkedFamiliesKernelFrame' Fm := by
  obtain ⟨⟨x0, h⟩, _⟩ := h
  exact ⟨x0, fun x hx hx0 i => (h x hx hx0 i).tiedSK⟩
theorem SecondLayerFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : SecondLayerFamilyClass Fm) : SecondChernLinkedClass Fm := h.c2sk.c2s
theorem group_compatibility_of_second_layer_family {eps : ℝ} (Fm : FamP eps) (h : SecondLayerFamilyClass Fm) : G.GroupCompatibilityFamily Fm := gTiedF_of_C2S_alt Fm h.c2s
end Formalism.L2
end
end
