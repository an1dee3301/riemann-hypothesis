module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA h h0
  exact GlobalTheory.constant_one_mem_cuspForms_of_wittIndex_zero (B := B) (sA := sA) (sB := sB) (t := t) h h0
