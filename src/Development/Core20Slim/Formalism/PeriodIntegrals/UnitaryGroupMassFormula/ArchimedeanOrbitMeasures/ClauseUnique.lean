module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst
public import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def aVal {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : ℝ :=
  Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
    Tw u' ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) / (X.muH u' Set.univ).toReal


def AinfValue : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
    (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) → ∀ hT, AinfClause X ψ u' hT (aVal X u')





end PI.AprimeInfW
