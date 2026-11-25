module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.KFiniteDetermined

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_kFin_of_mem_lowT {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {v : M.sm τ} (hv : v ∈ lowT M τ) : (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ :=
  (sSup_le (a := GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) fun A hA _ hw => ⟨A, hA.1, hw, hA.2.1⟩) hv

theorem restrInj : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.RestrInj D :=
  fun D θ hθ V S M J χ T hT h0 =>
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D V S M θ hθ (GlobalTheory.LowTypeRestriction.lowT_ne_bot M) J χ T hT
      fun v => h0 _ fun τ => mem_kFin_of_mem_lowT M τ (v τ).2

end GlobalTheory.KFiniteDetermined
