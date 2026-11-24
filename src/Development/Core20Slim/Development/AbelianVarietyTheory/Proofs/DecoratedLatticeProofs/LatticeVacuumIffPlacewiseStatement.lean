module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewise
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacuum_iff_placewise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v) → ∀ f, (Vac ψ S T LS LT P f ↔ IsThetaFunO ψ S T f ∧ ∀ v, P v → Vac ψ S T LS LT (· = v) f) ∧ (Vac ψ S T LS LT P f → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, Vac ψ S T LS LT P (om (g, h) f)) ∧ (Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f)) := by
  first | exact @GlobalTheory.VacLoc.vac_loc | exact GlobalTheory.VacLoc.vac_loc | (intros; apply GlobalTheory.VacLoc.vac_loc <;> assumption)
